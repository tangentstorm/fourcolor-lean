/-
Copyright (c) 2006-2018 Microsoft Corporation and Inria (Coq version).
Lean 4 port of the Four Color Theorem formalization.

The unavoidability theorem: assuming all 633 configurations are reducible,
no minimal counter-example to the Four Color Theorem exists. Following
unavoidability.v we proceed by the discharge method:

1. Every minimal counter-example is pentagonal (`MinimalCounterExample.pentagonal`,
   inherited from Birkhoff–Wernicke–Franklin via the small reducible configurations).
2. The discharge score is conserved (Euler formula): summing over the hypermap
   yields a positive total, hence some hub has positive discharge score
   (`posz_dscore`).
3. A hub with positive discharge score must have arity in `{5, 6, 7, 8, 9, 10, 11}`
   (`dscore_cap1` together with the discharge rules).
4. Each arity is excluded by the corresponding presentation file
   (`exclude5` … `exclude11`), which checks that one of the 633 reducible
   configurations fits, contradicting reducibility.
-/
import FourColor.Hypermap
import FourColor.Geometry
import FourColor.Coloring
import FourColor.Configurations

set_option maxHeartbeats 400000

open Hypermap FourColor

namespace FourColor

/-! ## Pentagonality of minimal counter-examples -/

/-- A minimal counter-example has no triangular face: arity-3 faces are
    reducible by Birkhoff's contraction (collapse a triangle ⇒ smaller
    planar bridgeless plain precubic hypermap). -/
theorem MinimalCounterExample.no_arity_three {G : Hypermap}
    (h : MinimalCounterExample G) : ∀ x : G.Dart, arity G x ≠ 3 :=
  sorry

/-- A minimal counter-example has no square face: arity-4 faces are reducible
    by Wernicke's contraction. -/
theorem MinimalCounterExample.no_arity_four {G : Hypermap}
    (h : MinimalCounterExample G) : ∀ x : G.Dart, arity G x ≠ 4 :=
  sorry

/-- A minimal counter-example has no degenerate face (arity 0, 1, or 2):
    such faces would imply a bridge or fixed-point, contradicting plainness
    or bridgelessness. -/
theorem MinimalCounterExample.arity_ge_three {G : Hypermap}
    (h : MinimalCounterExample G) : ∀ x : G.Dart, 3 ≤ arity G x :=
  sorry

/-- A minimal counter-example is pentagonal: every face has size ≥ 5.
    (Birkhoff–Wernicke–Franklin: configurations of arity 3 or 4 are reducible
    via the small initial configurations of `theConfigs`.) -/
theorem MinimalCounterExample.pentagonal {G : Hypermap}
    (h : MinimalCounterExample G) : Pentagonal G := by
  intro x
  have h3 := MinimalCounterExample.arity_ge_three h x
  have hne3 := MinimalCounterExample.no_arity_three h x
  have hne4 := MinimalCounterExample.no_arity_four h x
  omega

/-! ## Discharge score and the discharge method (discharge.v) -/

/-- The discharge score of a dart, encoding Euler's formula as a local
    redistribution. The exact definition follows discharge.v: it sums charge
    contributions over the surrounding part of the hub. -/
noncomputable def dscore {G : Hypermap} (_x : G.Dart) : ℤ :=
  sorry

/-- The total discharge over all node-orbit representatives is strictly
    positive on a planar bridgeless plain pentagonal hypermap. (Rocq
    `dscore_pos`: equals `60 - 6 · #|G|` plus boundary terms which sum to
    twelve under Euler.) -/
theorem totalDscore_pos {G : Hypermap} (h : MinimalCounterExample G) :
    0 < ∑ x : G.Dart, dscore x :=
  sorry

/-- If a finite sum is positive, some summand is positive. -/
theorem exists_pos_of_sum_pos {α : Type*} [Fintype α] (f : α → ℤ)
    (h : 0 < ∑ x, f x) : ∃ x, 0 < f x := by
  by_contra h_neg
  push_neg at h_neg
  have : ∑ x, f x ≤ 0 := by
    apply Finset.sum_nonpos; intro x _; exact h_neg x
  omega

/-- A vertex with strictly positive discharge score exists in every minimal
    counter-example. (Rocq `posz_dscore`: total discharge sums to a positive
    Euler-formula expression, so the maximum is positive.) -/
theorem posz_dscore {G : Hypermap} (h : MinimalCounterExample G) :
    ∃ x : G.Dart, 0 < dscore x :=
  exists_pos_of_sum_pos _ (totalDscore_pos h)

/-- A positive-discharge hub must have arity in `{5, …, 11}`. (Rocq
    `dscore_cap1`: bounded by the discharge rules of `discharge.v`.) -/
theorem dscore_pos_arity_le {G : Hypermap} (h : MinimalCounterExample G)
    {x : G.Dart} (hx : 0 < dscore x) :
    arity G x ≤ 11 :=
  sorry

/-! ## Per-arity exclusions (present5.v through present11.v) -/

/-- Arity-5 hub: any positive-discharge hub of arity 5 contains a fitting
    reducible configuration. (Rocq `exclude5` in present5.v.) -/
theorem exclude5 {G : Hypermap} (h : MinimalCounterExample G)
    (red : Reducibility) {x : G.Dart}
    (_hx : 0 < dscore x) (_har : arity G x = 5) : False :=
  sorry

/-- Arity-6 exclusion (Rocq `exclude6` in present6.v). -/
theorem exclude6 {G : Hypermap} (h : MinimalCounterExample G)
    (red : Reducibility) {x : G.Dart}
    (_hx : 0 < dscore x) (_har : arity G x = 6) : False :=
  sorry

/-- Arity-7 exclusion (Rocq `exclude7` in present7.v). -/
theorem exclude7 {G : Hypermap} (h : MinimalCounterExample G)
    (red : Reducibility) {x : G.Dart}
    (_hx : 0 < dscore x) (_har : arity G x = 7) : False :=
  sorry

/-- Arity-8 exclusion (Rocq `exclude8` in present8.v). -/
theorem exclude8 {G : Hypermap} (h : MinimalCounterExample G)
    (red : Reducibility) {x : G.Dart}
    (_hx : 0 < dscore x) (_har : arity G x = 8) : False :=
  sorry

/-- Arity-9 exclusion (Rocq `exclude9` in present9.v). -/
theorem exclude9 {G : Hypermap} (h : MinimalCounterExample G)
    (red : Reducibility) {x : G.Dart}
    (_hx : 0 < dscore x) (_har : arity G x = 9) : False :=
  sorry

/-- Arity-10 exclusion (Rocq `exclude10` in present10.v). -/
theorem exclude10 {G : Hypermap} (h : MinimalCounterExample G)
    (red : Reducibility) {x : G.Dart}
    (_hx : 0 < dscore x) (_har : arity G x = 10) : False :=
  sorry

/-- Arity-11 exclusion (Rocq `exclude11` in present11.v). -/
theorem exclude11 {G : Hypermap} (h : MinimalCounterExample G)
    (red : Reducibility) {x : G.Dart}
    (_hx : 0 < dscore x) (_har : arity G x = 11) : False :=
  sorry

/-! ## The unavoidability theorem (unavoidability.v) -/

/-- The unavoidability theorem: if all configurations in `theConfigs` are
    C-reducible, then no minimal counter-example exists. -/
theorem unavoidability :
    Reducibility → ∀ G : Hypermap, ¬ MinimalCounterExample G := by
  intro red G hMCE
  obtain ⟨x, hx⟩ := posz_dscore hMCE
  have h_pent : 5 ≤ arity G x := MinimalCounterExample.pentagonal hMCE x
  have h_le : arity G x ≤ 11 := dscore_pos_arity_le hMCE hx
  -- Case-split on arity ∈ {5, 6, 7, 8, 9, 10, 11}.
  have h_cases : arity G x = 5 ∨ arity G x = 6 ∨ arity G x = 7 ∨
      arity G x = 8 ∨ arity G x = 9 ∨ arity G x = 10 ∨ arity G x = 11 := by
    omega
  rcases h_cases with h | h | h | h | h | h | h
  · exact exclude5 hMCE red hx h
  · exact exclude6 hMCE red hx h
  · exact exclude7 hMCE red hx h
  · exact exclude8 hMCE red hx h
  · exact exclude9 hMCE red hx h
  · exact exclude10 hMCE red hx h
  · exact exclude11 hMCE red hx h

end FourColor
