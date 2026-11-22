// Tiny stack VM: interpreter for make.fun's tiny stack ISA v1 (kit ISA.md / vm.mjs).
// Runs every /input/<id>/{program,input}.bin, writes /output/<id>/{stdout.bin,exit.txt}.
// Pure Node stdlib; no clock, no network: two runs are byte-identical.
import {existsSync, mkdirSync, readdirSync, readFileSync, rmSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';

// [opcode, immediate bytes, pops, pushes]; any other byte traps 5.
const OPS = [
  [0, 0, 0, 0], [1, 1, 0, 1], [2, 4, 0, 1], [3, 0, 1, 0], [4, 0, 1, 2],
  [5, 0, 2, 2], [6, 0, 2, 3], [7, 0, 3, 3], [16, 0, 2, 1], [17, 0, 2, 1],
  [18, 0, 2, 1], [19, 0, 2, 1], [20, 0, 2, 1], [21, 0, 2, 1], [22, 0, 2, 1],
  [23, 0, 1, 1], [24, 0, 2, 1], [25, 0, 2, 1], [26, 0, 2, 1], [27, 0, 1, 1],
  [28, 0, 2, 1], [29, 0, 2, 1], [30, 0, 2, 1], [32, 0, 2, 1], [33, 0, 2, 1],
  [34, 0, 2, 1], [48, 2, 0, 0], [49, 2, 1, 0], [50, 2, 1, 0], [51, 2, 0, 0],
  [52, 0, 0, 0], [64, 0, 1, 1], [65, 0, 2, 0], [80, 0, 1, 0], [81, 0, 1, 0],
  [82, 0, 0, 1], [83, 0, 1, 0],
];
const IMM = new Uint8Array(256), POPS = new Uint8Array(256), PUSHES = new Uint8Array(256), KNOWN = new Uint8Array(256);
for (const [op, imm, pops, pushes] of OPS) { IMM[op] = imm; POPS[op] = pops; PUSHES[op] = pushes; KNOWN[op] = 1; }

// Traps: 2 underflow, 3 overflow, 4 div-zero, 5 bad opcode, 6 memory, 7 call depth, 8 RET empty, 9 pc, 10 steps, 11 output.
function execute(program, input) {
  const st = new Int32Array(256), calls = new Int32Array(64), mem = new Int32Array(256);
  const out = new Uint8Array(65536), n = program.length;
  let sp = 0, cp = 0, olen = 0, inPos = 0, pc = 0, steps = 0;
  const finish = (code) => ({bytes: out.subarray(0, olen), code});
  for (;;) {
    // Step order (ISA.md): step limit, pc range, opcode, immediate fit.
    if (steps === 1000000) return finish(10);
    if (pc < 0 || pc >= n) return finish(9);
    const op = program[pc];
    if (!KNOWN[op]) return finish(5);
    const imm = IMM[op];
    if (pc + imm >= n) return finish(9);
    steps++;
    if (sp < POPS[op]) return finish(2);
    if (sp - POPS[op] + PUSHES[op] > 256) return finish(3);
    const after = pc + 1 + imm;
    pc = after;
    switch (op) {
      case 0: return finish(0); // HALT
      case 1: st[sp++] = (program[after - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 2: // PUSH32, little-endian signed
        st[sp++] = program[after - 4] | (program[after - 3] << 8) | (program[after - 2] << 16) | (program[after - 1] << 24);
        break;
      case 3: sp--; break; // POP
      case 4: st[sp] = st[sp - 1]; sp++; break; // DUP
      case 5: { const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; break; } // SWAP
      case 6: st[sp] = st[sp - 2]; sp++; break; // OVER
      case 7: { const a = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = a; break; }
      case 23: st[sp - 1] = -st[sp - 1] | 0; break; // NEG, wraps at INT_MIN
      case 27: st[sp - 1] = ~st[sp - 1]; break; // NOT
      case 48: case 49: case 50: { // JMP / JZ / JNZ, signed 16-bit offset
        const rel = ((program[after - 2] | (program[after - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 48) { const v = st[--sp]; take = op === 49 ? v === 0 : v !== 0; }
        if (take) pc = after + rel;
        break;
      }
      case 51: // CALL, unsigned 16-bit target
        if (cp === 64) return finish(7);
        calls[cp++] = after;
        pc = program[after - 2] | (program[after - 1] << 8);
        break;
      case 52: // RET
        if (cp === 0) return finish(8);
        pc = calls[--cp];
        break;
      case 64: { // LOAD
        const addr = st[sp - 1];
        if (addr < 0 || addr >= 256) return finish(6);
        st[sp - 1] = mem[addr];
        break;
      }
      case 65: { // STORE: ( v addr -- ), address on top
        const addr = st[sp - 1], v = st[sp - 2];
        if (addr < 0 || addr >= 256) return finish(6);
        sp -= 2;
        mem[addr] = v;
        break;
      }
      case 80: { // PRINT: decimal ASCII; a trap writes nothing
        const s = String(st[sp - 1]);
        if (olen + s.length > 65536) return finish(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 81: // PUTC: one byte, v AND 255
        if (olen + 1 > 65536) return finish(11);
        out[olen++] = st[--sp] & 255;
        break;
      case 82: st[sp++] = inPos < input.length ? input[inPos++] : -1; break; // IN, -1 past end
      case 83: return finish(st[--sp] & 255); // EXIT with the low byte
      default: { // binary ops 16-22, 24-26, 28-30, 32-34
        const b = st[sp - 1], a = st[sp - 2];
        let r;
        switch (op) {
          case 16: r = (a + b) | 0; break; // ADD, wraps
          case 17: r = (a - b) | 0; break; // SUB, wraps
          case 18: r = Math.imul(a, b); break; // MUL, low 32 bits
          case 19: // DIV, toward zero; INT_MIN / -1 is INT_MIN
            if (b === 0) return finish(4);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
            break;
          case 20: // MOD, sign of a; x % -1 is 0
            if (b === 0) return finish(4);
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 21: // DIVU, unsigned quotient read back signed
            if (b === 0) return finish(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 22: // MODU, unsigned remainder read back signed
            if (b === 0) return finish(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 24: r = a & b; break;
          case 25: r = a | b; break;
          case 26: r = a ^ b; break;
          case 28: r = a << (b & 31); break; // SHL, low 5 bits only
          case 29: r = a >> (b & 31); break; // SHR, arithmetic
          case 30: r = (a >>> (b & 31)) | 0; break; // SHRU, logical
          case 32: r = a === b ? 1 : 0; break;
          case 33: r = a < b ? 1 : 0; break;
          case 34: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break; // LTU, unsigned
          default: throw new Error('unreachable opcode ' + op);
        }
        sp -= 2;
        st[sp++] = r;
      }
    }
  }
}

// Driver: one instance per input dir, sorted by id.
const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(INPUT_DIR).sort()) {
  const program = readFileSync(join(INPUT_DIR, id, 'program.bin'));
  const input = existsSync(join(INPUT_DIR, id, 'input.bin'))
    ? readFileSync(join(INPUT_DIR, id, 'input.bin')) : new Uint8Array(0);
  const result = execute(program, input);
  const dir = join(OUTPUT_DIR, id);
  mkdirSync(dir, {recursive: true});
  // Clear only the contents of the output directory, never the dir itself.
  for (const name of readdirSync(dir)) rmSync(join(dir, name), {force: true, recursive: true});
  writeFileSync(join(dir, 'stdout.bin'), result.bytes);
  writeFileSync(join(dir, 'exit.txt'), `${result.code}\n`);
}
