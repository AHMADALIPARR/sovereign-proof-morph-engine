<!-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0 -->
<!-- Copyright (C) 2026 Ahmad Ali Parr / SnapKitty Research Lab -->
# BQN programs: originals and checked variants

BQN is an executable model here, not proof authority. The CBQN interpreter
runs the `.bqn` sources; the sources themselves are not compiled to machine code.

Interpreter: CBQN commit b62079a ("built with FFI, singeli X86_64, replxx").

## Originals (verbatim in `bqn/`, header added)

CBQN stops at the first tokenizer error:

| file | CBQN output |
|---|---|
| omega_tensor.bqn | `Error: Unknown character: '𝕪'` |
| phi_replay.bqn | `Error: Unknown character: '\'` |
| twin_xgraph.bqn | `Error: Unknown characters: \\` |
| init_teleo.bqn | `Error: Unknown character: '\'` |

Further defects, fixed in `bqn/checked/` (each was hit when running under CBQN or found by reading the code):

1. `\` is not BQN scan. Scan is `` ` ``.
2. `𝕪` is not a BQN special name. The left argument is `𝕨`.
3. Names that start with a capital letter have function role, so `E_tensor ← array` fails with "Role of the two sides in assignment must match". The checked variants use lowercase names for data.
4. `Pi ← •math.pi`: CBQN has no `•math.pi`, and a capitalised name cannot hold a number. The checked variants use `pi ⇐ π`.
5. `•math.sqrt` does not exist. The checked variants use the primitive `√`.
6. `"f" •FRead "i64"` is not a valid read. CBQN's `•bit._cast` has no 64-bit integer width, so i64 data is read as 32-bit halves: low (unsigned) and high (signed). This is exact for |v| < 2^53.
7. `≢` of a flat read cannot recover V×D. The shape is stored in `shape.txt`.
8. `Replay_Kernel` contains `⇐`, which makes the block a namespace instead of a function.
9. `G_embs -˘ superposition` pairs the wrong ranks. Row-wise subtraction is `-⎉1`.
10. `G_embs ⊐˘ trace` is wrong. Token lookup is `g ⊐ > trace`.
11. `Pi` is undefined in twin_xgraph.bqn.
12. init_teleo.bqn uses `Active_Memory`, `Harmonic_Map`, `Replay_Kernel` and `Harmonic_Scalars` without defining them, and applies `+´` (lists only) to a matrix. The checked variant uses `+˝`. It defines Active_Memory as the last 16 forward-trace states; this is a choice the original does not specify.
13. omega_tensor's comment says `¯1⌽` rotates left. It rotates right: `(¯1⌽T)[n] = T[n-1]`.
14. `Harmonic_Map` parses as cos((φ·π·x)/2462). The checked library keeps that meaning.

## Inputs

`bqn/checked/gen_inputs.bqn DIR N V D` writes deterministic inputs using a Park–Miller LCG:

- intensity is 2462 | LCG(seed 12345);
- raw phase is 89·t;
- embeddings are in [-1, 1) (seed 777).

Default run: N = 7386 = 3·2462, V = 512, D = 64.

## Measured results (both CBQN builds print the same bytes)

See `docs/measurements/bqn.txt` for the full output.

- omega_tensor:
  - the torus phase is a permutation of Z_2462 over the first 2462 steps;
  - the ring delta is 89 at all 7386 steps;
  - 3712 coherent states.
- phi_replay:
  - 8 distinct tokens, longest run 12, 0 exact argmin ties;
  - the (token, phase) state cycle has μ = 1447 and λ = 2462.
- twin_xgraph:
  - forward cycle μ = 1447, λ = 2462; twin (EOS) cycle μ = 1, λ = 2462;
  - the forward and twin tokens differ at 3920 steps;
  - the midpoint snap has 3911 exact ties. The midpoint of two distinct rows is the same distance from both, and `⍋` takes the lower index.
- init_teleo:
  - the antipodal anchor (resonance cos(φπ·1231/2462) = −0.82534) is not a vocabulary row;
  - the antipodal twin trace and the EOS twin trace agree at 7385 of 7386 steps and merge from step 1;
  - both have μ = 1, λ = 2462 and 0 ties.

The state (token, phase mod 2462) is a finite deterministic system, so it is eventually periodic. The measured λ = 2462 equals the phase period. These runs therefore show that the φ-driven trace does form a loop.
