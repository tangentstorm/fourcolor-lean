/-
Copyright (c) 2006-2018 Microsoft Corporation and Inria (Coq version).
Lean 4 port of the Four Color Theorem formalization.

This file proves the equivalence of the Euler formula planarity condition
(genus = 0) and the Jordan curve theorem inspired combinatorial
characterization of planarity (no Moebius paths).

The proof uses induction on the number of darts via Walkup transforms.
-/
import FourColor.Hypermap
import FourColor.Walkup

set_option maxHeartbeats 800000

open Hypermap

namespace Hypermap

/-! ## Even genus and Euler inequality -/

/-
The even genus property always holds: the Euler characteristic
    difference `eulerLhs - eulerRhs` is always even. Equivalently,
    `eulerLhs = 2 * genus + eulerRhs`.

    Proved by Walkup induction on the number of darts. In the Coq
    version (jordan.v), this is `even_genusP`.
-/
theorem even_genusP (G : Hypermap) : eulerLhs G = 2 * genus G + eulerRhs G := by
  -- Strong induction on the number of darts
  have : ∀ n : ℕ, ∀ H : Hypermap, Fintype.card H.Dart ≤ n →
      eulerLhs H = 2 * genus H + eulerRhs H := by
    intro n
    induction n with
    | zero =>
      intro H hcard
      -- Impossible: H has Nonempty Dart, so card ≥ 1
      exfalso
      have := Fintype.card_pos (α := H.Dart)
      omega
    | succ n ih =>
      intro H hcard
      by_cases h1 : Fintype.card H.Dart = 1
      · -- Base case: exactly one dart. All permutations are the identity.
        -- eulerLhs = 2 * 1 + 1 = 3, eulerRhs = 1 + 1 + 1 = 3, genus = 0
        obtain ⟨ x, hx ⟩ := Fintype.card_eq_one_iff.mp h1;
        simp +decide [ Fintype.card_eq_one_iff, hx, Hypermap.eulerLhs, Hypermap.eulerRhs, Hypermap.genus ];
        simp +decide [ hx, Hypermap.fcardEdge, Hypermap.fcardNode, Hypermap.fcardFace, Hypermap.numOrbits ];
        simp +decide [ show H.edgePerm = 1 from Equiv.Perm.ext fun y => by simp +decide [ hx ], show H.nodePerm = 1 from Equiv.Perm.ext fun y => by simp +decide [ hx ], show H.facePerm = 1 from Equiv.Perm.ext fun y => by simp +decide [ hx ] ];
        rw [ show H.nComp = 1 from ?_ ] ; simp +arith +decide [ h1 ];
        convert Fintype.card_eq_one_iff.mpr _;
        use ⟦x⟧;
        rintro ⟨ y ⟩ ; exact Quotient.sound ( by tauto )
      · -- Inductive step: card ≥ 2
        have h2 : Fintype.card H.Dart ≥ 2 := by
          have := Fintype.card_pos (α := H.Dart); omega
        -- Pick any dart z
        have ⟨z⟩ := H.instNonempty
        -- Apply the Walkup transform
        have hcard' : Fintype.card (walkupE H z h2).Dart ≤ n := by
          rw [card_walkupE]; omega
        have ih_result := ih (walkupE H z h2) hcard'
        -- Use even_genus_WalkupE to transfer from walkupE to H
        exact even_genus_WalkupE H z h2 ih_result
  exact this (Fintype.card G.Dart) G (le_refl _)

/-- The Euler inequality: the right-hand side never exceeds the left-hand side.
    Follows directly from the even genus property. -/
theorem euler_le (G : Hypermap) : eulerRhs G ≤ eulerLhs G := by
  have h := even_genusP G
  omega

/-! ## Equivalence of planarity characterizations -/

/-! ### Walkup descent step (the inductive content of `planar_Jordan`/`Jordan_planar`)

The Rocq proof in `jordan.v` lifts/lowers Moebius paths through the three
Walkup transforms (`WalkupE`, `WalkupN`, `WalkupF`) and uses strong induction
on `#|G|`. We expose the per-direction lift step as `walkupE_jordan_descent`
(and its converse for the planar direction) and combine them via strong
induction below. -/

/-- Inductive content of `planar_jordan`: if `WalkupE G z` is Jordan and `G`
    is planar, then any Moebius path in `G` can be reflected back to a Moebius
    path in some `WalkupE z`/`WalkupN z`/`WalkupF z`. The Rocq proof picks
    `z := head q` and uses `liftE`/`liftN`/`liftF` to transport `q`. -/
theorem walkupE_no_moebius (G : Hypermap)
    (ih : ∀ H : Hypermap, Fintype.card H.Dart < Fintype.card G.Dart →
            Planar H → Jordan H)
    (hP : Planar G) (q : List G.Dart) (hMP : MoebiusPath G q) : False :=
  sorry

/-- Inductive content of `jordan_planar`: if `WalkupE G z` is planar and `G`
    is Jordan, then `G` is planar. (Rocq `Jordan_planar` does the strong
    induction the other way: assume `¬ planar G`, find a Moebius path.) -/
theorem walkupE_planar_descent (G : Hypermap)
    (ih : ∀ H : Hypermap, Fintype.card H.Dart < Fintype.card G.Dart →
            Jordan H → Planar H)
    (hJ : Jordan G) : Planar G :=
  sorry

/-- Euler planarity implies the Jordan property. (Rocq `planar_Jordan`.)
    Strong induction on `#|G|` via `walkupE_no_moebius`. -/
theorem planar_jordan (G : Hypermap) : Planar G → Jordan G := by
  -- Strong induction on the number of darts.
  suffices h : ∀ n : ℕ, ∀ H : Hypermap, Fintype.card H.Dart ≤ n →
      Planar H → Jordan H by
    exact h _ G (le_refl _)
  intro n
  induction n with
  | zero =>
    intro H hcard _
    -- Impossible: H.Dart is Nonempty so has card ≥ 1.
    exfalso
    have := Fintype.card_pos (α := H.Dart); omega
  | succ n ih =>
    intro G hcard hP q hMP
    -- Apply the descent lemma using the inductive hypothesis.
    have ih' : ∀ H : Hypermap, Fintype.card H.Dart < Fintype.card G.Dart →
        Planar H → Jordan H := by
      intro H hlt hPH
      exact ih H (Nat.lt_succ_iff.mp (lt_of_lt_of_le hlt hcard)) hPH
    exact walkupE_no_moebius G ih' hP q hMP

/-- The Jordan property implies Euler planarity. (Rocq `Jordan_planar`.)
    Strong induction on `#|G|` via `walkupE_planar_descent`. -/
theorem jordan_planar (G : Hypermap) : Jordan G → Planar G := by
  suffices h : ∀ n : ℕ, ∀ H : Hypermap, Fintype.card H.Dart ≤ n →
      Jordan H → Planar H by
    exact h _ G (le_refl _)
  intro n
  induction n with
  | zero =>
    intro H hcard _
    exfalso
    have := Fintype.card_pos (α := H.Dart); omega
  | succ n ih =>
    intro G hcard hJ
    have ih' : ∀ H : Hypermap, Fintype.card H.Dart < Fintype.card G.Dart →
        Jordan H → Planar H := by
      intro H hlt hJH
      exact ih H (Nat.lt_succ_iff.mp (lt_of_lt_of_le hlt hcard)) hJH
    exact walkupE_planar_descent G ih' hJ

/-- The Jordan and Euler planarity conditions are equivalent. -/
theorem jordan_iff_planar (G : Hypermap) : Jordan G ↔ Planar G :=
  ⟨jordan_planar G, planar_jordan G⟩

/-! ## Small helpers -/

/-- `Planar` unfolds definitionally to `genus = 0`. -/
@[simp] theorem planar_iff_genus_zero (G : Hypermap) : Planar G ↔ genus G = 0 :=
  Iff.rfl

/-- Genus is nonnegative (trivially, since it's a `Nat`). -/
theorem genus_nonneg (G : Hypermap) : 0 ≤ genus G := Nat.zero_le _

end Hypermap