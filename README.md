# fourcolor-lean

Lean 4 port of Georges Gonthier et al.'s formal Four Color Theorem proof, translated from Rocq/Coq. Upstream Rocq source: <https://github.com/rocq-community/fourcolor>.

## Progress

```
Overall port progress
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Core infrastructure    ████████████████░░░░  ~80%
fcardFace_cube         ██████████░░░░░░░░░░  ~50%  helpers ready, partition pending
walkupE_euler_compon.  ███░░░░░░░░░░░░░░░░░  ~15%  clean helpers; main theorem stalled
jordan_walkupE         ██░░░░░░░░░░░░░░░░░░  ~10%  blocked on walkupE_euler_components
jordan_planar          ██░░░░░░░░░░░░░░░░░░  ~10%
planar_jordan          ██░░░░░░░░░░░░░░░░░░  ~10%
Configurations (4)     █░░░░░░░░░░░░░░░░░░░  ~5%   30k Coq lines — moonshot
unavoidability         █░░░░░░░░░░░░░░░░░░░  ~5%   ~5k Coq lines
discretize_to_hypermap █░░░░░░░░░░░░░░░░░░░  ~5%   needs gridmap/matte port
compactness_extension  █░░░░░░░░░░░░░░░░░░░  ~5%   needs pmap/prefix_coloring
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Lines of Lean          ██████████░░░░░░░░░░  ~8% of Coq's 45k
Sorry count            ████████████████████  12 / 12 still open
Definitional gaps      ░░░░░░░░░░░░░░░░░░░░  0 / 2 remaining (both fixed ✓)
Heavy automation       ██████████████░░░░░░  ~70% replaced with explicit tactics
```

## Approach

This port aims to be a **complete proof**, mirroring the structure of the Rocq formalization file-for-file (see [`FourColor/README.md`](FourColor/README.md) for the architecture). The work runs as an autonomous loop:

1. **Audit.** Scan the port for open `sorry`s, definition gaps, and heavyweight automation (`aesop`, `grind`, `exact?`), cross-referenced against the upstream Rocq source in `rocq/fourcolor/`.
2. **Delegate.** Break work into narrow, self-contained lemmas and submit them to [Aristotle](https://aristotle.harmonic.fun) in parallel batches of 2–3 jobs (bigger theorems get decomposed into helper bundles rather than attempted whole).
3. **Review.** When jobs return, diff the patches, verify that proofs use only explicit fast-running tactics (no `aesop`/`grind`/`exact?`), build the project, and commit on pass. Any drift back toward high-cost automation gets rewritten by hand.
4. **Iterate.** Rinse and repeat every ~15 minutes. When the Aristotle queue stalls, equivalent helpers are proved locally.

**Design priorities:**
- **Readable proofs.** Each step should say what it's doing: `rcases`, `simp [specific_lemma]`, `rw`, `exact`, `omega`, `induction`, `cases`. Reserve `decide`/`simp +decide`/`omega` for decision procedures. Reject generic search tactics.
- **Definitional fidelity to Rocq.** Where the Rocq proof uses a specific construction (e.g. `mem2`, `Moebius_path`, `valid_contract`), the Lean version mirrors it. Early in the port two definitions (`MoebiusPath` and `ValidContract`/`CReducible`) were trivially true placeholders — both have since been replaced with real content.
- **No hidden sorries.** Every theorem on the main chain traces back to sorries that are explicitly listed in the progress bar; none are buried behind `True` propositions or `axiom`.

## Build

```powershell
elan
lake exe cache get
lake build
```

Math overview: see [`FourColor/README.md`](FourColor/README.md).

## Credits

Original Rocq formalization by Georges Gonthier et al. (Microsoft Research & INRIA, 2006-2018). Lean 4 port performed with substantial help from [Aristotle](https://aristotle.harmonic.fun), authored as commit co-author throughout the repository.
