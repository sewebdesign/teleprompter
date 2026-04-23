// ============================================================
//  Voice-Driven Teleprompter
//  Web Speech API + phonetic/fuzzy matching against script
// ============================================================

const $ = (id) => document.getElementById(id);
const editor = $('editor');
const prompter = $('prompter');
const scriptInput = $('script-input');
const scriptDisplay = $('script-display');
const statusEl = $('status');
const statusText = $('status-text');
const btnPlay = $('btn-play');
const btnEdit = $('btn-edit');
const btnReset = $('btn-reset');
const wordCountEl = $('word-count');
const errorBanner = $('error-banner');

let scriptWords = [];      // normalized array of words (for matching)
let displayWords = [];     // DOM span elements
let currentIndex = 0;      // pointer into script
let recognition = null;
let isRunning = false;
let lastProcessedTranscript = '';

// Tuning knob: strict mode raises the bar for fuzzy matching and recovery
// jumps. Flip via window.__tp.STRICT_MATCH to A/B compare at runtime.
let STRICT_MATCH = true;

// --- Normalization ---------------------------------------------------
function normalize(word) {
  return word
    .toLowerCase()
    .replace(/[^a-z0-9']/g, '')
    .replace(/'/g, '');
}

// --- Simple phonetic key (Metaphone-lite) ----------------------------
// Good enough to handle homophones & small mispronunciations for a demo.
function phoneticKey(word) {
  if (!word) return '';
  let w = word.toLowerCase().replace(/[^a-z]/g, '');
  if (!w) return '';

  // Drop silent leading letters
  w = w.replace(/^(kn|gn|pn|wr|ps)/, (m) => m[1]);
  if (w.startsWith('x')) w = 's' + w.slice(1);

  // Collapse common patterns
  w = w
    .replace(/[aeiouy]+/g, 'A')       // any vowel cluster -> A
    .replace(/ph/g, 'F')
    .replace(/[sc]h/g, 'X')
    .replace(/th/g, '0')
    .replace(/ck/g, 'K')
    .replace(/c(?=[iey])/g, 'S')
    .replace(/c/g, 'K')
    .replace(/q/g, 'K')
    .replace(/[sz]/g, 'S')
    .replace(/[dt]/g, 'T')
    .replace(/[bp]/g, 'P')
    .replace(/[fv]/g, 'F')
    .replace(/[gj]/g, 'J')
    .replace(/(.)\1+/g, '$1')         // collapse doubles
    .replace(/^A/, '');                // drop leading vowel sound

  return w;
}

// --- Levenshtein distance (small, fast) ------------------------------
function editDistance(a, b) {
  if (a === b) return 0;
  if (!a.length) return b.length;
  if (!b.length) return a.length;
  const dp = Array.from({ length: a.length + 1 }, (_, i) => [i]);
  for (let j = 1; j <= b.length; j++) dp[0][j] = j;
  for (let i = 1; i <= a.length; i++) {
    for (let j = 1; j <= b.length; j++) {
      const cost = a[i - 1] === b[j - 1] ? 0 : 1;
      dp[i][j] = Math.min(
        dp[i - 1][j] + 1,
        dp[i][j - 1] + 1,
        dp[i - 1][j - 1] + cost
      );
    }
  }
  return dp[a.length][b.length];
}

// --- Similarity between two words ------------------------------------
// Returns false on no match, or a string kind: 'exact' | 'phonetic' |
// 'prefix' | 'edit'. Callers that only need a boolean can rely on string
// truthiness. The kind matters because 'prefix' matches are provisional —
// advanceWithHeard defers them until the next heard word confirms.
function wordsMatch(heard, expected) {
  if (!heard || !expected) return false;
  if (heard === expected) return 'exact';

  const ph1 = phoneticKey(heard);
  const ph2 = phoneticKey(expected);
  if (ph1 && ph1 === ph2) return 'phonetic';

  // SR partials: interim results often arrive mid-word ("in" → "insane",
  // "fig" → "figma", "tele" → "teleprompter"). Accept a clean prefix
  // (by spelling OR phonetic key). Caller treats this as provisional.
  if (heard.length >= 2 && expected.length > heard.length && expected.startsWith(heard)) {
    return 'prefix';
  }
  if (ph1.length >= 2 && ph2.length > ph1.length && ph2.startsWith(ph1)) {
    return 'prefix';
  }

  // Edit distance tolerance (short words strict, longer words lenient)
  const maxLen = Math.max(heard.length, expected.length);
  const dist = editDistance(heard, expected);
  if (STRICT_MATCH) {
    if (maxLen <= 4) return false;
    if (maxLen <= 6) return dist <= 1 ? 'edit' : false;
    if (maxLen <= 9) return dist <= 2 ? 'edit' : false;
    return dist <= 3 ? 'edit' : false;
  }
  if (maxLen <= 3) return false;
  if (maxLen <= 5) return dist <= 1 ? 'edit' : false;
  if (maxLen <= 8) return dist <= 2 ? 'edit' : false;
  return dist <= 3 ? 'edit' : false;
}

// --- Core matcher ----------------------------------------------------
// Advance the script pointer using only NEW heard words since the last
// frame. We track the total number of heard words processed so far so we
// don't re-consume old words (which caused runaway lookahead jumps).
//
// For common short words ("the", "a", "is", "to", ...), we only allow a
// match at the exact current position — never via lookahead — because
// those words appear everywhere in a script and would cause false jumps.
//
// RECOVERY MODE: If the reader drifts off-script (tangent, improv), normal
// lookahead can't catch up. After a few consecutive failed matches, we
// search a wider forward window for a distinctive multi-word phrase from
// the heard buffer. If we find one, we jump the pointer forward.
const LOOKAHEAD = 4;
const RECOVERY_TRIGGER = 3;        // failed matches before recovery activates
const RECOVERY_WINDOW = 40;        // how far ahead to scan during recovery
const RECOVERY_MIN_PHRASE_STRICT = 3;   // strict: require 3-word alignment
const RECOVERY_MIN_PHRASE_LOOSE = 2;    // loose (legacy) behavior
const RECOVERY_MIN_CONTENT_STRICT = 2;  // strict: ≥2 content-word matches
const RECOVERY_MIN_CONTENT_LOOSE = 1;
const HEARD_BUFFER_SIZE = 12;      // rolling buffer of recent heard words

// --- Debug logging ---------------------------------------------------
// Only network/session lifecycle events are logged. Toggle at runtime:
// window.__tp.DEBUG = false
let DEBUG = false;
const dstyle = {
  sess:  'color:#6a9fb5',
  error: 'color:#e06b5a;font-weight:bold',
};
function dlog(kind, ...args) {
  if (!DEBUG) return;
  console.log('%c[' + kind + ']', dstyle[kind] || '', ...args);
}
// Intentional dev hook: flip DEBUG/STRICT_MATCH from the console to debug matching.
window.__tp = {
  get DEBUG() { return DEBUG; },
  set DEBUG(v) { DEBUG = !!v; console.log('[tp] DEBUG =', DEBUG); },
  get STRICT_MATCH() { return STRICT_MATCH; },
  set STRICT_MATCH(v) { STRICT_MATCH = !!v; console.log('[tp] STRICT_MATCH =', STRICT_MATCH); },
};
const COMMON_WORDS = new Set([
  'the','a','an','is','it','to','of','in','on','at','and','or','but',
  'so','i','you','we','he','she','they','my','your','our','their',
  'this','that','these','those','be','am','are','was','were','been',
  'do','does','did','have','has','had','for','as','with','by','from',
  'up','out','if','not','no','yes','me','us','them','him','her','his'
]);

let heardWordsProcessed = 0;  // how many heard words we've already consumed
let consecutiveMisses = 0;    // failed matches in a row (triggers recovery)
let heardBuffer = [];         // rolling buffer of recent normalized heard words
let lastHighlightedIndex = -1; // tracks DOM state so updateHighlight can diff
let pendingPrefix = null;     // unconfirmed prefix match: {scriptIdx, heardWord}
let isScrubbing = false;      // true while user is dragging the canvas to reposition

// Bound the heard-word array so per-event work doesn't grow with session length.
const PRUNE_THRESHOLD = 500;
const PRUNE_KEEP = 100;
function maybePruneHeard() {
  if (pastFinalizedWords.length <= PRUNE_THRESHOLD) return;
  const dropCount = pastFinalizedWords.length - PRUNE_KEEP;
  if (heardWordsProcessed < dropCount) return; // never drop unprocessed
  pastFinalizedWords = pastFinalizedWords.slice(dropCount);
  heardWordsProcessed -= dropCount;
}

// Look for a distinctive phrase match in the forward window.
// Returns the script index to jump to, or -1 if no confident match found.
function findRecoveryJump() {
  const minPhrase = STRICT_MATCH ? RECOVERY_MIN_PHRASE_STRICT : RECOVERY_MIN_PHRASE_LOOSE;
  const minContent = STRICT_MATCH ? RECOVERY_MIN_CONTENT_STRICT : RECOVERY_MIN_CONTENT_LOOSE;

  if (heardBuffer.length < minPhrase) {
    return -1;
  }

  const windowEnd = Math.min(
    scriptWords.length,
    currentIndex + RECOVERY_WINDOW
  );

  let bestScore = 0;
  let bestJumpTo = -1;

  // For each possible starting position in the heard buffer,
  // and each possible starting position in the script window,
  // count consecutive forward matches.
  for (let heardStart = 0; heardStart < heardBuffer.length; heardStart++) {
    for (let scriptStart = currentIndex; scriptStart < windowEnd; scriptStart++) {
      let matchLen = 0;
      let contentMatches = 0;
      let hasDistinctive = false;  // strict: ≥1 matched word must be distinctive

      while (
        heardStart + matchLen < heardBuffer.length &&
        scriptStart + matchLen < windowEnd
      ) {
        const hw = heardBuffer[heardStart + matchLen];
        const sw = scriptWords[scriptStart + matchLen];
        if (wordsMatch(hw, sw)) {
          matchLen++;
          if (!COMMON_WORDS.has(hw)) contentMatches++;
          // Distinctive: length ≥ 6 OR phonetic key ≥ 4 chars (the latter
          // catches dense-consonant words like "script" where phoneticKey
          // collapses vowels to 'A').
          if (sw.length >= 6 || phoneticKey(sw).length >= 4) {
            hasDistinctive = true;
          }
        } else {
          break;
        }
      }

      const passes = STRICT_MATCH
        ? (matchLen >= minPhrase && contentMatches >= minContent && hasDistinctive)
        : (matchLen >= minPhrase && contentMatches >= minContent);

      if (passes) {
        const distance = scriptStart - currentIndex;
        const heardRecency = heardStart;
        // Strict: content matches multiply (so 3-word/2-content beats
        // 2-word/1-content); stronger distance penalty to prefer staying close.
        const score = STRICT_MATCH
          ? matchLen * 10 * Math.max(1, contentMatches)
            - distance * 0.2
            - heardRecency * 0.5
          : matchLen * 10 + contentMatches * 5
            - distance * 0.1
            - heardRecency * 0.5;

        if (score > bestScore) {
          bestScore = score;
          bestJumpTo = scriptStart + matchLen;
        }
      }
    }
  }

  return bestJumpTo;
}

function advanceWithHeard(heardWords) {
  if (isScrubbing) return;
  if (!heardWords.length) return;
  if (currentIndex >= scriptWords.length) return;

  const newWords = heardWords.slice(heardWordsProcessed);
  if (!newWords.length) return;

  for (const heard of newWords) {
    heardWordsProcessed++;
    if (currentIndex >= scriptWords.length) break;

    const normHeard = normalize(heard);
    if (!normHeard) continue;

    // Add to rolling heard buffer for recovery mode
    heardBuffer.push(normHeard);
    if (heardBuffer.length > HEARD_BUFFER_SIZE) heardBuffer.shift();

    // Resolve any pending (provisional) prefix match from the previous word.
    // The prefix is "confirmed" iff this word matches the script position
    // immediately after the prefix-matched one. Otherwise the prefix is
    // discarded and we process this word normally against currentIndex.
    if (pendingPrefix !== null) {
      const confirmIdx = pendingPrefix.scriptIdx + 1;
      const confirmExpected = scriptWords[confirmIdx];
      const confirmKind = confirmIdx < scriptWords.length
        ? wordsMatch(normHeard, confirmExpected)
        : false;
      // Only solid kinds confirm — another prefix isn't enough evidence.
      if (confirmKind && confirmKind !== 'prefix') {
        currentIndex = confirmIdx + 1;
        consecutiveMisses = 0;
        pendingPrefix = null;
        continue;
      }
      pendingPrefix = null;
      // Fall through: process this word normally against currentIndex (unchanged).
    }

    const isCommon = COMMON_WORDS.has(normHeard);
    const maxLook = isCommon
      ? 1
      : Math.min(LOOKAHEAD, scriptWords.length - currentIndex);

    let matched = false;
    let matchKind = false;
    let matchOffset = 0;
    const oldIdx = currentIndex;
    for (let i = 0; i < maxLook; i++) {
      const expected = scriptWords[currentIndex + i];
      const kind = wordsMatch(normHeard, expected);
      if (kind) {
        matched = true;
        matchKind = kind;
        matchOffset = i;
        break;
      }
    }

    if (matched) {
      const matchedScriptIdx = oldIdx + matchOffset;
      // Prefix matches at the exact current position are provisional.
      // Prefix at a lookahead offset > 0 would mean skipping real words on
      // weak evidence — too risky to defer; reject and treat as miss.
      if (matchKind === 'prefix' && matchOffset === 0) {
        pendingPrefix = { scriptIdx: matchedScriptIdx, heardWord: normHeard };
        continue;
      }
      if (matchKind === 'prefix') {
        matched = false;
      } else {
        currentIndex = matchedScriptIdx + 1;
        consecutiveMisses = 0;
      }
    }

    if (!matched) {
      consecutiveMisses++;
      if (consecutiveMisses >= RECOVERY_TRIGGER) {
        const jumpTo = findRecoveryJump();
        if (jumpTo > currentIndex) {
          currentIndex = jumpTo;
          consecutiveMisses = 0;
          heardBuffer = [];
          pendingPrefix = null;
        }
      }
    }
  }

  updateHighlight();
  maybePruneHeard();
}

// --- Rendering -------------------------------------------------------
function renderScript(text) {
  // Preserve structure: split into tokens, keep punctuation attached
  scriptDisplay.innerHTML = '';
  scriptWords = [];
  displayWords = [];

  const tokens = text.match(/\S+|\s+/g) || [];
  let wordIdx = 0;

  for (const tok of tokens) {
    if (/^\s+$/.test(tok)) {
      // Two-or-more newlines = paragraph break; render as vertical gap.
      // Single newlines / spaces collapse to one space (normal wrapping).
      if ((tok.match(/\n/g) || []).length >= 2) {
        scriptDisplay.appendChild(document.createElement('br'));
        scriptDisplay.appendChild(document.createElement('br'));
      } else {
        scriptDisplay.appendChild(document.createTextNode(' '));
      }
      continue;
    }
    const span = document.createElement('span');
    span.className = 'word upcoming';
    span.textContent = tok;
    span.dataset.idx = wordIdx;
    scriptDisplay.appendChild(span);

    const normalized = normalize(tok);
    if (normalized) {
      scriptWords.push(normalized);
      displayWords.push(span);
      wordIdx++;
    } else {
      // punctuation-only token: keep as non-word
      span.classList.remove('upcoming');
      span.classList.add('spoken');
    }
  }

  wordCountEl.textContent = scriptWords.length;
}

function updateWordClasses() {
  if (lastHighlightedIndex === currentIndex) return;
  if (currentIndex < lastHighlightedIndex) {
    // Backward (reset/edit/scrub). Full re-pass; rare, no perf concern.
    displayWords.forEach((el, i) => {
      el.classList.remove('current', 'upcoming', 'spoken');
      if (i < currentIndex) el.classList.add('spoken');
      else if (i === currentIndex) el.classList.add('current');
      else el.classList.add('upcoming');
    });
  } else {
    // Forward: mark [lastHighlightedIndex, currentIndex) as spoken,
    // then promote currentIndex to current. Handles single-word advance,
    // multi-word lookahead skips, and recovery jumps in one pass.
    const from = Math.max(0, lastHighlightedIndex);
    for (let i = from; i < currentIndex && i < displayWords.length; i++) {
      const el = displayWords[i];
      el.classList.remove('current', 'upcoming');
      el.classList.add('spoken');
    }
    const cur = displayWords[currentIndex];
    if (cur) {
      cur.classList.remove('upcoming', 'spoken');
      cur.classList.add('current');
    }
  }
  lastHighlightedIndex = currentIndex;
}

function centerCurrentWord() {
  const current = displayWords[currentIndex] || displayWords[displayWords.length - 1];
  if (!current) return;
  const mainRect = prompter.getBoundingClientRect();
  const wordRect = current.getBoundingClientRect();
  const currentTransform = getComputedStyle(scriptDisplay).transform;
  let currentY = 0;
  if (currentTransform && currentTransform !== 'none') {
    const m = new DOMMatrix(currentTransform);
    currentY = m.m42;
  }
  const wordCenter = wordRect.top + wordRect.height / 2;
  const target = mainRect.top + mainRect.height / 2;
  const delta = wordCenter - target;
  const newY = currentY - delta;
  scriptDisplay.style.transform = `translateY(${newY}px)`;
}

function updateHighlight() {
  updateWordClasses();
  centerCurrentWord();
}

// --- Speech recognition ---------------------------------------------
// We accumulate finalized text across multiple recognition sessions
// because Chrome's continuous recognition auto-stops periodically.
let pastFinalizedWords = [];        // stable words from completed SR sessions
let currentSessionFinalWords = [];  // finalized words from the live SR session
let restartTimer = null;            // debounce timer for recognition restarts
let awaitingResume = false;         // true after a restart attempt, until first onresult

function initRecognition() {
  const SR = window.SpeechRecognition || window.webkitSpeechRecognition;
  if (!SR) {
    showError('Your browser does not support the Web Speech API. Try Chrome or Edge.');
    return null;
  }
  const r = new SR();
  r.continuous = true;
  r.interimResults = true;
  r.lang = 'en-US';
  r.maxAlternatives = 1;

  r.onresult = (evt) => {
    if (awaitingResume) {
      dlog('sess', 'recognition resumed (first result after restart)');
      awaitingResume = false;
    }
    let sessionFinal = '';
    let sessionInterim = '';
    for (let i = 0; i < evt.results.length; i++) {
      const res = evt.results[i];
      if (res.isFinal) sessionFinal += res[0].transcript + ' ';
      else sessionInterim += res[0].transcript + ' ';
    }

    currentSessionFinalWords = sessionFinal.trim().split(/\s+/).filter(Boolean);
    const interimWords = sessionInterim.trim().split(/\s+/).filter(Boolean);
    if (!currentSessionFinalWords.length && !interimWords.length && !pastFinalizedWords.length) return;

    const allWords = pastFinalizedWords.concat(currentSessionFinalWords, interimWords);
    advanceWithHeard(allWords);
  };

  r.onerror = (e) => {
    dlog('error', 'SR error:', e.error);
    if (e.error === 'no-speech' || e.error === 'aborted') return;
    if (e.error === 'not-allowed' || e.error === 'service-not-allowed') {
      // Permission denied — stop everything immediately and do not restart
      isRunning = false;
      if (restartTimer) { clearTimeout(restartTimer); restartTimer = null; }
      showError('Microphone access denied. Please allow mic access in your browser settings and try again.');
      stop();
    } else if (e.error === 'network') {
      showError('Network error. Web Speech API requires an internet connection in Chrome.');
    } else {
      if (DEBUG) console.warn('Speech error:', e.error);
    }
  };

  r.onend = () => {
    // Chrome auto-stops after silence/timeout. Carry finalized text forward
    // so the next session's indexing doesn't duplicate or lose words.
    dlog('sess', 'recognition onend — restarting:', isRunning);
    if (!isRunning) return;

    pastFinalizedWords = pastFinalizedWords.concat(currentSessionFinalWords);
    currentSessionFinalWords = [];

    // Debounced restart — prevents Chrome from re-prompting permissions
    // when onend fires rapidly (which happens on some errors).
    if (restartTimer) clearTimeout(restartTimer);
    restartTimer = setTimeout(() => {
      if (!isRunning || !recognition) return;
      try {
        recognition.start();
        awaitingResume = true;
        dlog('sess', 'recognition restart attempted');
      } catch (err) {
        // "already started" is fine to ignore; anything else we bail
        if (!String(err.message || '').includes('already started')) {
          dlog('error', 'restart failed:', err.message || err);
          isRunning = false;
        }
      }
    }, 250);
  };

  return r;
}

function showError(msg) {
  errorBanner.textContent = msg;
  errorBanner.classList.add('show');
  statusEl.classList.add('error');
  statusText.textContent = 'error';
  setTimeout(() => errorBanner.classList.remove('show'), 6000);
}

// --- Control flow ----------------------------------------------------
function start() {
  const text = scriptInput.value.trim();
  if (!text) {
    scriptInput.focus();
    return;
  }

  renderScript(text);
  currentIndex = 0;
  heardWordsProcessed = 0;
  consecutiveMisses = 0;
  heardBuffer = [];
  pastFinalizedWords = [];
  currentSessionFinalWords = [];
  lastHighlightedIndex = -1;
  pendingPrefix = null;
  updateHighlight();

  editor.classList.add('hidden');
  prompter.classList.add('active');

  recognition = initRecognition();
  if (!recognition) return;

  try {
    recognition.start();
    isRunning = true;
    statusEl.classList.add('active');
    statusEl.classList.remove('error');
    statusText.textContent = 'listening';
    btnPlay.textContent = '■  Stop';
    btnPlay.setAttribute('aria-label', 'Stop');
    btnPlay.classList.add('recording');
    btnEdit.disabled = true;
    btnReset.disabled = false;
  } catch (err) {
    showError('Could not start microphone.');
  }
}

function stop() {
  isRunning = false;
  if (restartTimer) { clearTimeout(restartTimer); restartTimer = null; }
  if (recognition) {
    try { recognition.stop(); } catch(_) {}
    recognition = null;
  }
  isScrubbing = false;
  prompter.classList.remove('scrubbing');
  statusEl.classList.remove('active');
  statusText.textContent = 'stopped';
  btnPlay.textContent = '▶  Resume';
  btnPlay.setAttribute('aria-label', 'Resume');
  btnPlay.classList.remove('recording');
  btnEdit.disabled = false;
  btnReset.disabled = false;
}

function reset() {
  stop();
  currentIndex = 0;
  heardWordsProcessed = 0;
  consecutiveMisses = 0;
  heardBuffer = [];
  pastFinalizedWords = [];
  currentSessionFinalWords = [];
  lastHighlightedIndex = -1;
  pendingPrefix = null;
  isScrubbing = false;
  prompter.classList.remove('scrubbing');
  updateHighlight();
  statusText.textContent = 'idle';
  btnPlay.textContent = '▶  Play';
  btnPlay.setAttribute('aria-label', 'Play');
}

function editScript() {
  stop();
  prompter.classList.remove('active');
  editor.classList.remove('hidden');
  scriptDisplay.style.transform = 'translateY(0)';
  prompter.classList.remove('scrubbing');
  currentIndex = 0;
  heardWordsProcessed = 0;
  consecutiveMisses = 0;
  heardBuffer = [];
  pastFinalizedWords = [];
  currentSessionFinalWords = [];
  lastHighlightedIndex = -1;
  pendingPrefix = null;
  isScrubbing = false;
  btnPlay.textContent = '▶  Play';
  btnPlay.setAttribute('aria-label', 'Play');
  btnEdit.disabled = true;
  btnReset.disabled = true;
  statusText.textContent = 'idle';
  statusEl.classList.remove('active', 'error');
}

// --- Events ---------------------------------------------------------
btnPlay.addEventListener('click', () => {
  if (isRunning) stop();
  else start();
});

btnEdit.addEventListener('click', editScript);
btnReset.addEventListener('click', reset);

// Live word count in editor + persist to localStorage
const SCRIPT_STORAGE_KEY = 'tp.scriptText';
scriptInput.addEventListener('input', () => {
  const count = (scriptInput.value.match(/\S+/g) || []).length;
  wordCountEl.textContent = count;
  try { localStorage.setItem(SCRIPT_STORAGE_KEY, scriptInput.value); } catch (_) {}
});

// Restore saved script if present, otherwise prefill a sample so users can try immediately.
const SAMPLE_SCRIPT = `Welcome to the voice teleprompter demo. As I read this text aloud, each word will light up the moment it's recognized, and the page will gently scroll to keep my place.

The magic here isn't perfect transcription. It's alignment. The software already knows what I'm supposed to say, so even if the recognition makes a small mistake, fuzzy and phonetic matching keep everything on track.

Try reading this at a natural pace. Pause for a moment and notice that the script waits for you. Speed up, and it will keep up. That's exactly the behavior a real teleprompter needs.`;
let savedScript = null;
try { savedScript = localStorage.getItem(SCRIPT_STORAGE_KEY); } catch (_) {}
scriptInput.value = (savedScript != null && savedScript.length) ? savedScript : SAMPLE_SCRIPT;
wordCountEl.textContent = (scriptInput.value.match(/\S+/g) || []).length;

// ============================================================
//  Width + Size Controls
// ============================================================
const stageInner = $('stage-inner');
const widthSlider = $('width-slider');
const widthValue = $('width-value');
const sizeSlider = $('size-slider');
const sizeValue = $('size-value');
const dragLeft = $('drag-left');
const dragRight = $('drag-right');

const MIN_WIDTH = 400;
const MAX_WIDTH = 1300;

const WIDTH_STORAGE_KEY = 'tp.stageWidth';
const SIZE_STORAGE_KEY = 'tp.prompterSize';

function setStageWidth(px) {
  const clamped = Math.max(MIN_WIDTH, Math.min(MAX_WIDTH, px));
  stageInner.style.setProperty('--stage-width', clamped + 'px');
  widthSlider.value = clamped;
  widthValue.textContent = clamped;
  try { localStorage.setItem(WIDTH_STORAGE_KEY, String(clamped)); } catch (_) {}
  if (prompter.classList.contains('active')) {
    requestAnimationFrame(updateHighlight);
  }
}

function setPrompterSize(px) {
  document.documentElement.style.setProperty('--prompter-size', px + 'px');
  sizeValue.textContent = px;
  sizeSlider.value = px;
  try { localStorage.setItem(SIZE_STORAGE_KEY, String(px)); } catch (_) {}
  if (prompter.classList.contains('active')) {
    requestAnimationFrame(updateHighlight);
  }
}

widthSlider.addEventListener('input', (e) => setStageWidth(parseInt(e.target.value, 10)));
sizeSlider.addEventListener('input', (e) => setPrompterSize(parseInt(e.target.value, 10)));

// --- Drag handle logic (mouse + touch) ---
function setupDragHandle(handle, side) {
  let dragging = false;
  let startX = 0;
  let startWidth = 0;

  const onDown = (clientX) => {
    dragging = true;
    startX = clientX;
    startWidth = stageInner.getBoundingClientRect().width;
    handle.classList.add('dragging');
    document.body.style.cursor = 'ew-resize';
    document.body.style.userSelect = 'none';
  };

  const onMove = (clientX) => {
    if (!dragging) return;
    const delta = clientX - startX;
    // The stage is centered, so both sides move symmetrically: multiply delta by 2.
    const widthDelta = side === 'right' ? delta * 2 : -delta * 2;
    setStageWidth(startWidth + widthDelta);
  };

  const onUp = () => {
    if (!dragging) return;
    dragging = false;
    handle.classList.remove('dragging');
    document.body.style.cursor = '';
    document.body.style.userSelect = '';
  };

  handle.addEventListener('mousedown', (e) => { e.preventDefault(); onDown(e.clientX); });
  window.addEventListener('mousemove', (e) => onMove(e.clientX));
  window.addEventListener('mouseup', onUp);

  // Keyboard: left/right arrows adjust width for accessibility.
  // Each side grows the stage symmetrically, so the step is halved on the
  // per-key delta to match the drag behavior (delta * 2 in onMove).
  handle.addEventListener('keydown', (e) => {
    if (e.key !== 'ArrowLeft' && e.key !== 'ArrowRight') return;
    e.preventDefault();
    const step = e.shiftKey ? 50 : 20;
    const current = stageInner.getBoundingClientRect().width;
    const grow = (side === 'right' && e.key === 'ArrowRight') ||
                 (side === 'left'  && e.key === 'ArrowLeft');
    setStageWidth(current + (grow ? step : -step));
  });

  handle.addEventListener('touchstart', (e) => {
    if (e.touches.length === 1) { e.preventDefault(); onDown(e.touches[0].clientX); }
  }, { passive: false });
  window.addEventListener('touchmove', (e) => {
    if (e.touches.length === 1) onMove(e.touches[0].clientX);
  }, { passive: true });
  window.addEventListener('touchend', onUp);
  window.addEventListener('touchcancel', onUp);
}

setupDragHandle(dragLeft, 'left');
setupDragHandle(dragRight, 'right');

// Initialize defaults (restore saved values if present)
const savedWidth = parseInt(localStorage.getItem(WIDTH_STORAGE_KEY) || '', 10);
const savedSize = parseInt(localStorage.getItem(SIZE_STORAGE_KEY) || '', 10);
setStageWidth(Number.isFinite(savedWidth) ? savedWidth : 900);
setPrompterSize(Number.isFinite(savedSize) ? savedSize : 36);

// Re-align on window resize while prompting
window.addEventListener('resize', () => {
  if (prompter.classList.contains('active')) updateHighlight();
});

// ============================================================
//  Click-and-drag scrub on the prompter canvas
// ============================================================
// Pull the script up or down with the mouse/finger to reposition. Drag
// distance maps to word index in reading order — not to the word under the
// reading line — so each tiny pixel of motion nudges the highlight forward
// or backward by exactly one word rather than jumping a whole line at a
// time when a new row of text crosses the reading line. The canvas snaps to
// keep the current word on the reading line as it steps. On release the
// matcher's rolling buffer is flushed so SR picks up from the new position.
function setupCanvasScrub() {
  let dragging = false;
  let startY = 0;
  let startIdx = 0;
  let pixelsPerWord = 12;
  const DRAG_THRESHOLD = 4;

  // Pixels of drag required to advance one word. Average reading-path
  // density: total vertical span of the rendered text divided by word count.
  // At typical body copy this works out to ~6–10 px/word, which matches the
  // natural pace of the finger (drag N px ≈ canvas moves N px on average).
  const computePixelsPerWord = () => {
    if (displayWords.length <= 1) return 12;
    const first = displayWords[0].getBoundingClientRect();
    const last = displayWords[displayWords.length - 1].getBoundingClientRect();
    const span = Math.abs((last.top + last.height / 2) - (first.top + first.height / 2));
    if (span <= 0) return 12;
    return Math.max(4, span / (displayWords.length - 1));
  };

  const onDown = (clientY) => {
    if (!prompter.classList.contains('active')) return;
    dragging = true;
    startY = clientY;
    startIdx = currentIndex;
    pixelsPerWord = computePixelsPerWord();
    prompter.classList.add('scrubbing');
    document.body.style.userSelect = 'none';
  };

  const onMove = (clientY) => {
    if (!dragging) return;
    const delta = clientY - startY;
    if (Math.abs(delta) < DRAG_THRESHOLD && !isScrubbing) return;
    isScrubbing = true;

    // Finger up (delta < 0) => advance; finger down (delta > 0) => rewind.
    const wordOffset = Math.round(-delta / pixelsPerWord);
    const maxIdx = Math.max(0, displayWords.length - 1);
    const targetIdx = Math.max(0, Math.min(maxIdx, startIdx + wordOffset));

    if (targetIdx !== currentIndex) {
      currentIndex = targetIdx;
      updateWordClasses();
      centerCurrentWord();
    }
  };

  const onUp = () => {
    if (!dragging) return;
    dragging = false;
    document.body.style.userSelect = '';
    prompter.classList.remove('scrubbing');
    if (isScrubbing) {
      isScrubbing = false;
      centerCurrentWord();
      // Flush matcher memory so SR picks up from the new position.
      heardBuffer = [];
      consecutiveMisses = 0;
      pendingPrefix = null;
      heardWordsProcessed = pastFinalizedWords.length + currentSessionFinalWords.length;
      lastHighlightedIndex = currentIndex;
    }
  };

  prompter.addEventListener('mousedown', (e) => {
    if (!prompter.classList.contains('active')) return;
    if (e.button !== 0) return; // left button only
    e.preventDefault();
    onDown(e.clientY);
  });
  window.addEventListener('mousemove', (e) => onMove(e.clientY));
  window.addEventListener('mouseup', onUp);

  prompter.addEventListener('touchstart', (e) => {
    if (!prompter.classList.contains('active')) return;
    if (e.touches.length !== 1) return;
    e.preventDefault();
    onDown(e.touches[0].clientY);
  }, { passive: false });
  window.addEventListener('touchmove', (e) => {
    if (!dragging || e.touches.length !== 1) return;
    e.preventDefault();
    onMove(e.touches[0].clientY);
  }, { passive: false });
  window.addEventListener('touchend', onUp);
  window.addEventListener('touchcancel', onUp);
}

setupCanvasScrub();
