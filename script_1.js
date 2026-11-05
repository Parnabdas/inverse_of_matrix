// ==MATH==
const absB = x => x < 0n ? -x : x;
const gcdB = (a, b) => { a = absB(a); b = absB(b); while (b) { [a, b] = [b, a % b]; } return a; };

class Frac {
  constructor(n, d = 1n) {
    if (d === 0n) throw new Error('Division by zero');
    if (d < 0n) { n = -n; d = -d; }
    const g = gcdB(n, d) || 1n;
    this.n = n / g; this.d = d / g;
  }
  add(o) { return new Frac(this.n * o.d + o.n * this.d, this.d * o.d); }
  sub(o) { return new Frac(this.n * o.d - o.n * this.d, this.d * o.d); }
  mul(o) { return new Frac(this.n * o.n, this.d * o.d); }
  div(o) { if (o.n === 0n) throw new Error('Division by zero'); return new Frac(this.n * o.d, this.d * o.n); }
  neg()  { return new Frac(-this.n, this.d); }
  isZero() { return this.n === 0n; }
  eq(o) { return this.n === o.n && this.d === o.d; }
  toString() { return this.d === 1n ? String(this.n) : this.n + '/' + this.d; }
}
const ZERO = new Frac(0n), ONE = new Frac(1n);

function parseDec(s) {
  s = s.trim();
  const m = /^([+-]?)(\d*)(?:\.(\d*))?$/.exec(s);
  if (!m || (m[2] === '' && (m[3] === undefined || m[3] === ''))) throw new Error('bad');
  const frac = m[3] || '';
  let n = BigInt((m[2] || '0') + frac);
  if (m[1] === '-') n = -n;
  return new Frac(n, 10n ** BigInt(frac.length));
}
function parseNum(s) {
  s = String(s).trim().replace(/\u2212/g, '-');
  if (s === '') return ZERO;
  if (s.includes('/')) {
    const parts = s.split('/');
    if (parts.length !== 2) throw new Error('bad');
    const a = parseDec(parts[0]), b = parseDec(parts[1]);
    if (b.isZero()) throw new Error('zero denominator');
    return a.div(b);
  }
  return parseDec(s);
}

const minorOf = (M, i, j) => M.filter((_, r) => r !== i).map(row => row.filter((_, c) => c !== j));
function det(M) {
  const n = M.length;
  if (n === 1) return M[0][0];
  if (n === 2) return M[0][0].mul(M[1][1]).sub(M[0][1].mul(M[1][0]));
  let s = ZERO;
  for (let j = 0; j < n; j++) {
    if (M[0][j].isZero()) continue;
    const t = M[0][j].mul(det(minorOf(M, 0, j)));
    s = (j % 2 === 0) ? s.add(t) : s.sub(t);
  }
  return s;
}
const transpose = M => M[0].map((_, j) => M.map(row => row[j]));
function mulM(A, B) {
  return A.map((row, i) => B[0].map((_, j) => row.reduce((s, a, k) => s.add(a.mul(B[k][j])), ZERO)));
}
// division without reducing (to show the "before simplifying" fraction)
function divRaw(a, b) {
  let n = a.n * b.d, d = a.d * b.n;
  if (d < 0n) { n = -n; d = -d; }
  return { n, d };
}
// ==/MATH==

// ---------- helpers for display ----------
const $ = s => document.querySelector(s);
const esc = s => String(s).replace(/&/g, '&amp;').replace(/"/g, '&quot;').replace(/</g, '&lt;').replace(/>/g, '&gt;');

function fh(f) {
  const neg = f.n < 0n, an = neg ? -f.n : f.n;
  const sg = neg ? '<span class="sg">−</span>' : '';
  if (f.d === 1n) return `<span class="fv">${sg}${an}</span>`;
  return `<span class="fv">${sg}<span class="frac"><span class="t">${an}</span><span class="b">${f.d}</span></span></span>`;
}
const pf = f => f.n < 0n ? `(${fh(f)})` : fh(f);

function mat(M, o = {}) {
  const r = M.length, c = M[0].length;
  let h = `<div class="mat${o.small ? ' sm' : ''}"><div class="grid" style="--cols:${c}">`;
  for (let i = 0; i < r; i++) for (let j = 0; j < c; j++) {
    const cls = o.cls ? o.cls(i, j) : '';
    const body = o.render ? o.render(i, j) : fh(M[i][j]);
    let attrs = '';
    if (o.act) {
      const [si, sj] = o.sel ? o.sel(i, j) : [i, j];
      attrs = ` data-act="${o.act}" data-k="${o.k}" data-si="${si}" data-sj="${sj}"`;
    }
    h += `<div class="c ${cls}" data-i="${i}" data-j="${j}"${attrs}>${body}</div>`;
  }
  return h + '</div></div>';
}

function detExplicit(M) {
  const m = M.length, v = det(M);
  if (m === 1) return `<b>${fh(v)}</b> <span class="hint">(a 1×1 determinant is just the number itself)</span>`;
  if (m === 2) {
    const a = M[0][0], b = M[0][1], c = M[1][0], d = M[1][1];
    const p = a.mul(d), q = b.mul(c);
    return `${pf(a)}×${pf(d)} − ${pf(b)}×${pf(c)} = ${fh(p)} − ${pf(q)} = <b>${fh(v)}</b>`;
  }
  return `<b>${fh(v)}</b> <span class="hint">(a ${m}×${m} determinant, found by expanding along its first row the same way as in Step 2)</span>`;
}

// ---------- state ----------
const STEPS = ['Matrix', 'Determinant', 'Minors', 'Cofactors', 'Adjoint', 'Inverse', 'Check'];
const KINDS = ['minor', 'cof', 'adj', 'inv', 'ver'];
const S = { n: 3, raw: [], step: 0, ready: false, sing: false, bad: [], timer: null, timerKind: null, sel: {}, rev: {} };

function exampleMatrix(n) {
  if (n === 2) return [[4, 7], [2, 6]];
  if (n === 3) return [[3, 0, 2], [2, 0, -2], [0, 1, 1]];
  return Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => i === j ? 2 : (Math.abs(i - j) === 1 ? 1 : 0)));
}
const toRaw = M => M.map(r => r.map(String));
S.raw = toRaw(exampleMatrix(3));

function resetExplorers() {
  const n = S.n;
  KINDS.forEach(k => {
    S.sel[k] = { i: 0, j: 0 };
    S.rev[k] = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => i === 0 && j === 0));
  });
}

function compute(A) {
  S.A = A;
  S.det = det(A);
  S.sing = S.det.isZero();
  S.minors = A.map((row, i) => row.map((_, j) => det(minorOf(A, i, j))));
  S.cof = S.minors.map((row, i) => row.map((v, j) => ((i + j) % 2 ? v.neg() : v)));
  S.adj = transpose(S.cof);
  S.inv = S.sing ? null : S.adj.map(row => row.map(v => v.div(S.det)));
  S.prod = S.sing ? null : mulM(A, S.inv);
  resetExplorers();
}

function prepare() {
  const n = S.n, A = [], bad = [];
  for (let i = 0; i < n; i++) {
    const row = [];
    for (let j = 0; j < n; j++) {
      try { row.push(parseNum(S.raw[i][j])); } catch (e) { bad.push([i, j]); row.push(ZERO); }
    }
    A.push(row);
  }
  S.bad = bad;
  if (bad.length) { S.ready = false; return false; }
  compute(A);
  S.ready = true;
  return true;
}

function stopTimer() { if (S.timer) clearInterval(S.timer); S.timer = null; S.timerKind = null; }

// ---------- views ----------
const head = (idx, title, lead) => `<h2><span class="badge">${idx}</span> ${title}</h2><p class="lead">${lead}</p>`;

function viewInput() {
  const n = S.n;
  const sizes = [2, 3, 4, 5, 6].map(k => `<button class="chip${k === n ? ' on' : ''}" data-act="size" data-n="${k}">${k}×${k}</button>`).join('');
  let cells = '';
  for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
    const bad = S.bad.some(([a, b]) => a === i && b === j) ? ' bad' : '';
    cells += `<input class="cellin${bad}" data-i="${i}" data-j="${j}" value="${esc(S.raw[i][j])}" placeholder="0" autocomplete="off" aria-label="row ${i + 1}, column ${j + 1}">`;
  }
  const err = S.bad.length
    ? `<div class="err">⚠️ ${S.bad.slice(0, 3).map(([i, j]) => `row ${i + 1}, column ${j + 1}`).join('; ')}${S.bad.length > 3 ? '…' : ''} ${S.bad.length === 1 ? "isn't" : "aren't"} a valid number. Use things like <code>3</code>, <code>-2</code>, <code>1/2</code> or <code>0.25</code>.</div>` : '';
  return head(1, 'Enter your square matrix',
    'Choose a size and type your numbers. You can use whole numbers (<code>3</code>, <code>-2</code>), fractions (<code>1/2</code>) or decimals (<code>0.25</code>, which we turn into the fraction <code>1/4</code>). An empty box counts as 0.')
    + `<div class="row"><span class="lbl">Size:</span>${sizes}</div>`
    + `<div class="inmat"><div class="mat"><div class="grid" style="--cols:${n}">${cells}</div></div></div>`
    + `<div class="row"><span class="lbl">Quick fill:</span>
        <button class="btn ghost" data-act="example">Example</button>
        <button class="btn ghost" data-act="random">Random</button>
        <button class="btn ghost" data-act="identity">Identity</button>
        <button class="btn ghost" data-act="singular">Singular (no inverse)</button>
        <button class="btn ghost" data-act="clear">Clear</button></div>`
    + err;
}

function viewDet() {
  const n = S.n, A = S.A, d = S.det;
  const lead = 'The <b>determinant</b> is one special number made from the matrix. It decides everything: if it is <b>0</b>, there is <b>no inverse</b>. Otherwise the inverse is the adjoint divided by this number.';
  let body;
  if (n === 2) {
    body = `<div class="work"><div class="wtitle">Shortcut for a 2×2 matrix: det = a·d − b·c</div>
      ${mat(A, { cls: (r, c) => r === c ? 'keep' : 'gone' })}
      <p class="hint">Green diagonal multiplied, minus the red diagonal multiplied.</p>
      <p class="eq">det(A) = ${detExplicit(A)}</p></div>`;
  } else {
    let cards = '', terms = [];
    for (let j = 0; j < n; j++) {
      const a = A[0][j], sub = minorOf(A, 0, j), mv = det(sub), pos = j % 2 === 0;
      const term = pos ? a.mul(mv) : a.mul(mv).neg();
      terms.push(term);
      cards += `<div class="tcard"><div class="ttl">Term ${j + 1}: a<sub>1${j + 1}</sub> = ${fh(a)}</div>
        <div class="trow">${mat(A, { small: true, cls: (r, c) => (r === 0 || c === j) ? 'gone' : 'keep' })}<span class="op">→</span>${mat(sub, { small: true, cls: () => 'keep' })}</div>
        <p>Minor M<sub>1${j + 1}</sub> = ${detExplicit(sub)}</p>
        <p>Sign: (−1)<sup>1+${j + 1}</sup> = <b>${pos ? '+1' : '−1'}</b></p>
        <p class="eq">Term = (${pos ? '+1' : '−1'}) × ${pf(a)} × ${pf(mv)} = <b>${fh(term)}</b></p></div>`;
    }
    body = `<div class="note info">We <b>expand along the first row</b>: multiply each number in row 1 by its cofactor and add everything up.
        <div class="hint">det(A) = a₁₁·C₁₁ + a₁₂·C₁₂ + … (Steps 3 and 4 explain minors and cofactors in detail.)</div></div>
      <div class="cards">${cards}</div>
      <div class="work"><div class="wtitle">Add the terms</div>
      <p class="eq">det(A) = ${terms.map(pf).join(' + ')} = <b>${fh(d)}</b></p></div>`;
  }
  const verdict = S.sing
    ? `<div class="note bad"><b>det(A) = 0</b>, so this matrix is <b>singular</b>: it has no inverse. You can still look at the minors, cofactors and adjoint to see how they work.</div>`
    : `<div class="note ok"><b>det(A) = ${fh(d)} ≠ 0</b>, so the inverse exists. Let's build it!</div>`;
  return head(2, 'The determinant', lead) + body + verdict;
}

// ----- explorer plumbing -----
function resMat(kind, R, selMap, extra) {
  const { i, j } = S.sel[kind], rev = S.rev[kind];
  return mat(R, {
    k: kind, act: 'pick', sel: selMap,
    cls: (r, c) => {
      const [a, b] = selMap(r, c);
      return (extra ? extra(r, c) + ' ' : '') + (a === i && b === j ? 'sel ' : '') + (rev[a][b] ? 'pop' : 'hid');
    },
    render: (r, c) => { const [a, b] = selMap(r, c); return rev[a][b] ? fh(R[r][c]) : '?'; }
  });
}
function controls(kind) {
  const n = S.n, cnt = S.rev[kind].flat().filter(Boolean).length;
  const playing = S.timer && S.timerKind === kind;
  return `<div class="ctrl">
    <button class="btn" data-act="play" data-k="${kind}">${playing ? '⏸ Pause' : '▶ Auto-play'}</button>
    <button class="btn ghost" data-act="next" data-k="${kind}">Next cell</button>
    <button class="btn ghost" data-act="all" data-k="${kind}">Reveal all</button>
    <button class="btn ghost" data-act="reset" data-k="${kind}">Reset</button>
    <span class="prog">${cnt} of ${n * n} cells revealed</span></div>`;
}
function frame(kind, body, done) {
  const all = S.rev[kind].flat().every(Boolean);
  return body + controls(kind) + (all ? `<div class="note ok">${done}</div>` : '');
}
const panel = (cap, html) => `<div class="panel"><div class="cap">${cap}</div>${html}</div>`;
const op = s => `<div class="op">${s}</div>`;

function viewMinor() {
  const k = 'minor', { i, j } = S.sel[k], A = S.A, sub = minorOf(A, i, j);
  const left = mat(A, { k, act: 'pick', cls: (r, c) => r === i && c === j ? 'gone sel' : (r === i || c === j ? 'gone' : 'keep') });
  const body = head(3, 'Matrix of Minors',
    'The <b>minor</b> M<sub>ij</sub> of a number: <b>cover up its row and column</b>, then take the determinant of the smaller matrix that remains. Do this for every position. Click any cell, or press <b>Next cell</b>.')
    + `<div class="panels">${panel('Original matrix A (click a cell)', left)}${op('→')}${panel('Matrix of minors M', resMat(k, S.minors, (r, c) => [r, c]))}</div>`
    + `<div class="work"><div class="wtitle">Working for M<sub>${i + 1}${j + 1}</sub></div>
        <p>Cover <b>row ${i + 1}</b> and <b>column ${j + 1}</b> (red). The green numbers are what is left:</p>
        ${mat(sub, { small: true, cls: () => 'keep' })}
        <p class="eq">M<sub>${i + 1}${j + 1}</sub> = ${detExplicit(sub)}</p></div>`;
  return frame(k, body, '🎉 All minors found. Next we attach a + or − sign to each one.');
}

function viewCof() {
  const k = 'cof', { i, j } = S.sel[k];
  const signs = S.A.map((row, r) => row.map((_, c) => (r + c) % 2 ? ONE.neg() : ONE));
  const left = mat(S.minors, { k, act: 'pick', cls: (r, c) => r === i && c === j ? 'sel' : '' });
  const sg = mat(signs, { k, act: 'pick', cls: (r, c) => ((r + c) % 2 ? 'neg ' : 'pos ') + (r === i && c === j ? 'sel' : ''), render: (r, c) => (r + c) % 2 ? '−' : '+' });
  const m = S.minors[i][j], pos = (i + j) % 2 === 0, res = S.cof[i][j];
  const body = head(4, 'Cofactor Matrix',
    'A <b>cofactor</b> is a minor with a sign attached: C<sub>ij</sub> = (−1)<sup>i+j</sup> × M<sub>ij</sub>. The signs follow a <b>checkerboard</b> pattern that starts with + in the top-left corner. Click a cell or press <b>Next cell</b>.')
    + `<div class="panels">${panel('Minors M', left)}${op('×')}${panel('Sign pattern', sg)}${op('=')}${panel('Cofactors C', resMat(k, S.cof, (r, c) => [r, c]))}</div>`
    + `<div class="work"><div class="wtitle">Working for C<sub>${i + 1}${j + 1}</sub></div>
        <p>Position (${i + 1}, ${j + 1}): ${i + 1} + ${j + 1} = ${i + j + 2}, which is <b>${pos ? 'even → +1' : 'odd → −1'}</b>.</p>
        <p class="eq">C<sub>${i + 1}${j + 1}</sub> = (−1)<sup>${i + j + 2}</sup> × M<sub>${i + 1}${j + 1}</sub> = (${pos ? '+1' : '−1'}) × ${pf(m)} = <b>${fh(res)}</b></p></div>`;
  return frame(k, body, '🎉 Cofactor matrix complete. One more move: flip it (transpose) to get the adjoint.');
}

function viewAdj() {
  const k = 'adj', { i, j } = S.sel[k];
  const left = mat(S.cof, { k, act: 'pick', cls: (r, c) => r === i && c === j ? 'sel' : (r === i ? 'rowhl' : '') });
  const right = resMat(k, S.adj, (r, c) => [c, r], (r, c) => c === i ? 'colhl' : '');
  const body = head(5, 'Adjoint (Adjugate)',
    'The <b>adjoint</b> adj(A) is the <b>transpose</b> of the cofactor matrix: rows become columns. The number in row i, column j moves to row j, column i.')
    + `<div class="panels">${panel('Cofactor matrix C', left)}${op('ᵀ →')}${panel('adj(A) = Cᵀ', right)}</div>`
    + `<div class="work"><div class="wtitle">What just moved?</div>
        <p>C<sub>${i + 1}${j + 1}</sub> = ${fh(S.cof[i][j])} was in <b>row ${i + 1}, column ${j + 1}</b>. In the adjoint it sits in <b>row ${j + 1}, column ${i + 1}</b>.</p>
        <p class="hint">So the whole row ${i + 1} of C (shaded) becomes column ${i + 1} of adj(A) (shaded).</p></div>`;
  return frame(k, body, '🎉 Adjoint done. The last step: divide it by the determinant.');
}

function viewInv() {
  if (S.sing) {
    return head(6, 'The inverse', 'The inverse formula is A⁻¹ = adj(A) ÷ det(A).')
      + `<div class="note bad"><b>Stop: det(A) = 0.</b> We cannot divide by zero, so this matrix has <b>no inverse</b>. (Mathematicians call it <i>singular</i>.)</div>
         <div class="row"><button class="btn" data-act="go" data-k="0">Change the matrix</button></div>`;
  }
  const k = 'inv', { i, j } = S.sel[k], d = S.det;
  const a = S.adj[i][j], res = S.inv[i][j], raw = divRaw(a, d);
  const changed = raw.n !== res.n || raw.d !== res.d;
  const left = mat(S.adj, { k, act: 'pick', cls: (r, c) => r === i && c === j ? 'sel' : '' });
  const body = head(6, 'The Inverse',
    `Now we use the formula <b>A⁻¹ = (1 ÷ det(A)) × adj(A)</b>. Here det(A) = ${fh(d)}, so every entry of adj(A) gets divided by ${fh(d)}.`)
    + `<div class="panels">${panel('1 ÷ det(A)', `<div class="c" style="font-size:1.3rem">${fh(ONE.div(d))}</div>`)}${op('×')}${panel('adj(A)', left)}${op('=')}${panel('A⁻¹', resMat(k, S.inv, (r, c) => [r, c]))}</div>`
    + `<div class="work"><div class="wtitle">Working for entry (${i + 1}, ${j + 1})</div>
        <p class="eq">adj<sub>${i + 1}${j + 1}</sub> ÷ det(A) = ${pf(a)} ÷ ${pf(d)}${changed ? ` = ${fh(raw)}` : ''} = <b>${fh(res)}</b></p>
        <p class="hint">${changed ? 'Then we simplify the fraction to lowest terms.' : 'Dividing by a fraction means multiplying by its flip. Already in lowest terms.'}</p></div>`;
  return frame(k, body, '🎉 You found A⁻¹! Go to the next step to double-check it.');
}

function viewVer() {
  const k = 'ver', { i, j } = S.sel[k], n = S.n;
  const left = mat(S.A, { k, act: 'pick', sel: (r, c) => [r, j], cls: (r, c) => r === i ? 'rowhl' : '' });
  const mid = mat(S.inv, { k, act: 'pick', sel: (r, c) => [i, c], cls: (r, c) => c === j ? 'colhl' : '' });
  const prods = [];
  for (let t = 0; t < n; t++) prods.push(S.A[i][t].mul(S.inv[t][j]));
  const terms = prods.map((_, t) => `${pf(S.A[i][t])}×${pf(S.inv[t][j])}`).join(' + ');
  const vals = prods.map(pf).join(' + ');
  const body = head(7, 'Check: A × A⁻¹ = I',
    'A real inverse must satisfy <b>A × A⁻¹ = I</b>, the identity matrix (1s on the diagonal, 0s everywhere else). Each cell of the product is <b>row × column</b>: multiply matching numbers and add. Click cells or press <b>Next cell</b>.')
    + `<div class="panels">${panel('A', left)}${op('×')}${panel('A⁻¹', mid)}${op('=')}${panel('A × A⁻¹', resMat(k, S.prod, (r, c) => [r, c]))}</div>`
    + `<div class="work"><div class="wtitle">Working for cell (${i + 1}, ${j + 1})</div>
        <p>Row ${i + 1} of A with column ${j + 1} of A⁻¹:</p>
        <p class="eq">${terms}</p>
        <p class="eq">= ${vals} = <b>${fh(S.prod[i][j])}</b></p>
        <p class="hint">${i === j ? 'On the diagonal we expect 1.' : 'Off the diagonal we expect 0.'}</p></div>`;
  const isId = S.prod.every((row, r) => row.every((v, c) => v.eq(r === c ? ONE : ZERO)));
  return frame(k, body, isId ? '✅ The product is the identity matrix, so A⁻¹ is correct!' : '⚠️ The product is not the identity. Something is off.');
}

// ---------- render & navigation ----------
function render() {
  $('#nav').innerHTML = STEPS.map((t, k) =>
    `<button class="pill${k === S.step ? ' on' : ''}${k < S.step ? ' done' : ''}" data-act="go" data-k="${k}" ${S.ready && S.sing && k > 5 ? 'disabled' : ''}><span>${k + 1}</span>${t}</button>`).join('');
  $('#stage').innerHTML = [viewInput, viewDet, viewMinor, viewCof, viewAdj, viewInv, viewVer][S.step]();
  const last = S.step === 6 || (S.ready && S.sing && S.step === 5);
  $('#back').disabled = S.step === 0;
  $('#next').textContent = S.step === 0 ? 'Start →' : (last ? 'Finished ✓' : 'Next →');
  $('#next').disabled = last;
}
function go(k, scroll = true) {
  stopTimer();
  if (k > 0 && !S.ready && !prepare()) { S.step = 0; render(); return; }
  if (S.ready && S.sing && k > 5) k = 5;
  S.step = Math.max(0, Math.min(6, k));
  render();
  if (scroll) $('#card').scrollIntoView({ behavior: 'smooth', block: 'start' });
}

function pick(kind, i, j) { S.sel[kind] = { i, j }; S.rev[kind][i][j] = true; }
function nextCell(kind) {
  const rev = S.rev[kind];
  for (let i = 0; i < S.n; i++) for (let j = 0; j < S.n; j++) if (!rev[i][j]) { pick(kind, i, j); return true; }
  return false;
}
function setSize(n) {
  const old = S.raw;
  S.raw = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => (old[i] && old[i][j] !== undefined) ? old[i][j] : ''));
  S.n = n; S.ready = false; S.bad = []; render();
}
function fill(M) { S.raw = toRaw(M); S.ready = false; S.bad = []; render(); }

document.addEventListener('click', e => {
  const el = e.target.closest('[data-act]');
  if (!el || el.disabled) return;
  const a = el.dataset.act, k = el.dataset.k;
  switch (a) {
    case 'go': go(+k); break;
    case 'prev': go(S.step - 1); break;
    case 'nextstep': go(S.step + 1); break;
    case 'size': setSize(+el.dataset.n); break;
    case 'example': fill(exampleMatrix(S.n)); break;
    case 'identity': fill(Array.from({ length: S.n }, (_, i) => Array.from({ length: S.n }, (_, j) => i === j ? 1 : 0))); break;
    case 'clear': S.raw = Array.from({ length: S.n }, () => Array(S.n).fill('')); S.ready = false; S.bad = []; render(); break;
    case 'singular': {
      const M = exampleMatrix(S.n); M[S.n - 1] = M[0].map(x => x * 2); fill(M); break;
    }
    case 'random': {
      let M, tries = 0;
      do {
        M = Array.from({ length: S.n }, () => Array.from({ length: S.n }, () => Math.floor(Math.random() * 9) - 4));
        tries++;
      } while (det(M.map(r => r.map(v => new Frac(BigInt(v))))).isZero() && tries < 60);
      fill(M); break;
    }
    case 'pick': stopTimer(); pick(k, +el.dataset.si, +el.dataset.sj); render(); break;
    case 'next': stopTimer(); nextCell(k); render(); break;
    case 'all': stopTimer(); S.rev[k] = S.rev[k].map(r => r.map(() => true)); render(); break;
    case 'reset': stopTimer(); S.rev[k] = S.rev[k].map((r, i) => r.map((_, j) => i === 0 && j === 0)); S.sel[k] = { i: 0, j: 0 }; render(); break;
    case 'play':
      if (S.timer && S.timerKind === k) { stopTimer(); render(); break; }
      stopTimer();
      if (S.rev[k].flat().every(Boolean)) { S.rev[k] = S.rev[k].map((r, i) => r.map((_, j) => i === 0 && j === 0)); S.sel[k] = { i: 0, j: 0 }; }
      S.timerKind = k;
      S.timer = setInterval(() => { if (!nextCell(k)) stopTimer(); render(); }, 1200);
      if (!nextCell(k)) stopTimer();
      render();
      break;
  }
});

document.addEventListener('input', e => {
  const el = e.target;
  if (!el.classList || !el.classList.contains('cellin')) return;
  S.raw[+el.dataset.i][+el.dataset.j] = el.value;
  S.ready = false; S.sing = false; S.bad = [];
  el.classList.remove('bad');
});

render();
