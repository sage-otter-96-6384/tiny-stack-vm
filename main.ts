// Tiny stack VM: a faithful port of the kit's reference VM (ISA.md / vm.mjs).
// Reads /input/<id>/{program.bin,input.bin}, writes /output/<id>/{stdout.bin,exit.txt}.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// opcode -> imm*100 + pops*10 + pushes (unknown opcodes absent -> trap 5)
const T = { 0: 0, 1: 101, 2: 401, 3: 10, 4: 12, 5: 22, 6: 23, 7: 33,
  16: 21, 17: 21, 18: 21, 19: 21, 20: 21, 21: 21, 22: 21, 23: 11, 24: 21, 25: 21,
  26: 21, 27: 11, 28: 21, 29: 21, 30: 21, 32: 21, 33: 21, 34: 21,
  48: 200, 49: 210, 50: 210, 51: 200, 52: 0, 64: 11, 65: 20, 80: 10, 81: 10, 82: 1, 83: 10 };

function run(p, inp) {
  const n = p.length;
  const D = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256);
  const out = new Uint8Array(65536), tmp = new Uint8Array(12);
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  // Pre-decode once: opcode, decoded immediate, next pc, pops, pushes per address.
  const O = new Int32Array(n), A = new Int32Array(n), N = new Int32Array(n),
    P = new Int32Array(n), U = new Int32Array(n);
  for (let i = 0; i < n; i++) {
    const t = T[p[i]];
    if (t === undefined) { O[i] = -1; continue; }
    const imm = (t / 100) | 0;
    O[i] = p[i]; P[i] = ((t / 10) | 0) % 10; U[i] = t % 10; N[i] = i + 1 + imm;
    if (imm === 1) A[i] = (p[i + 1] << 24) >> 24;
    else if (imm === 4) A[i] = p[i + 1] | (p[i + 2] << 8) | (p[i + 3] << 16) | (p[i + 4] << 24);
    else if (imm === 2) A[i] = p[i] === 51 ? p[i + 1] | (p[i + 2] << 8) : ((p[i + 1] | (p[i + 2] << 8)) << 16) >> 16;
  }
  const done = (e) => ({ o: out.slice(0, olen), e });
  for (;;) {
    if (steps === 1e6) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = O[pc], a = A[pc], nx = N[pc];
    if (op < 0) return done(5);
    if (nx > n) return done(9);
    steps++;
    const pops = P[pc], push = U[pc];
    if (sp < pops) return done(2);
    if (sp - pops + push > 256) return done(3);
    pc = nx;
    switch (op) {
      case 0: return done(0);
      case 1: case 2: D[sp++] = a; break;
      case 3: sp--; break;
      case 4: D[sp] = D[sp - 1]; sp++; break;
      case 5: { const x = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = x; break; }
      case 6: D[sp] = D[sp - 2]; sp++; break;
      case 7: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 23: D[sp - 1] = -D[sp - 1] | 0; break;
      case 27: D[sp - 1] = ~D[sp - 1]; break;
      case 16: case 17: case 18: case 19: case 20: case 21: case 22: case 24: case 25:
      case 26: case 28: case 29: case 30: case 32: case 33: case 34: {
        const b = D[sp - 1], a = D[sp - 2];
        let r;
        if (op === 16) r = (a + b) | 0;
        else if (op === 17) r = (a - b) | 0;
        else if (op === 18) r = Math.imul(a, b);
        else if (op === 19) { if (!b) return done(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
        else if (op === 20) { if (!b) return done(4); r = b === -1 ? 0 : (a % b) | 0; }
        else if (op === 21) { if (!b) return done(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 22) { if (!b) return done(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 24) r = a & b;
        else if (op === 25) r = a | b;
        else if (op === 26) r = a ^ b;
        else if (op === 28) r = a << (b & 31);
        else if (op === 29) r = a >> (b & 31);
        else if (op === 30) r = (a >>> (b & 31)) | 0;
        else if (op === 32) r = a === b ? 1 : 0;
        else if (op === 33) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2; D[sp++] = r; break;
      }
      case 48: case 49: case 50: {
        let take = true;
        if (op !== 48) { const v = D[--sp]; take = op === 49 ? v === 0 : v !== 0; }
        if (take) pc = nx + a;
        break;
      }
      case 51:
        if (csp === 64) return done(7);
        C[csp++] = nx;
        pc = a;
        break;
      case 52:
        if (!csp) return done(8);
        pc = C[--csp];
        break;
      case 64: {
        const a = D[sp - 1];
        if (a < 0 || a > 255) return done(6);
        D[sp - 1] = M[a];
        break;
      }
      case 65: {
        const a = D[sp - 1], v = D[sp - 2];
        if (a < 0 || a > 255) return done(6);
        sp -= 2; M[a] = v;
        break;
      }
      case 80: {
        const v = D[sp - 1];
        let u = v < 0 ? -v : v, j = 12;
        if (!u) tmp[--j] = 48;
        else while (u > 0) { tmp[--j] = 48 + (u % 10); u = (u / 10) | 0; }
        if (v < 0) tmp[--j] = 45;
        if (olen + 12 - j > 65536) return done(11);
        sp--; out.set(tmp.subarray(j), olen); olen += 12 - j;
        break;
      }
      case 81:
        if (olen + 1 > 65536) return done(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 82:
        D[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 83:
        return done(D[--sp] & 255);
    }
  }
}

for (const id of readdirSync(IN).sort()) {
  const r = run(readFileSync(join(IN, id, 'program.bin')), readFileSync(join(IN, id, 'input.bin')));
  mkdirSync(join(OUT, id), { recursive: true });
  writeFileSync(join(OUT, id, 'stdout.bin'), r.o);
  writeFileSync(join(OUT, id, 'exit.txt'), r.e + '\n');
}
