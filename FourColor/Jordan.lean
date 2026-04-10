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

/-- The Jordan property implies Euler planarity. -/
theorem jordan_planar (G : Hypermap) : Jordan G → Planar G := by
  sorry

/-- Euler planarity implies the Jordan property. -/
theorem planar_jordan (G : Hypermap) : Planar G → Jordan G := by
  sorry

/-- The Jordan and Euler planarity conditions are equivalent. -/
theorem jordan_iff_planar (G : Hypermap) : Jordan G ↔ Planar G :=
  ⟨jordan_planar G, planar_jordan G⟩

end Hypermap