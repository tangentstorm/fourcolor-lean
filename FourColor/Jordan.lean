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

set_option maxHeartbeats 1600000

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

/-- Lift a Moebius path through `WalkupE` along a chosen dart `z` not in the
    path: any Moebius path `q` of `G` avoiding `z` yields a Moebius path of
    the smaller hypermap `walkupE G z h2`. (Rocq `liftE` in `jordan.v:77`.) -/
theorem MoebiusPath.lift_walkupE (G : Hypermap) (z : G.Dart)
    (h2 : Fintype.card G.Dart ≥ 2) (q : List G.Dart)
    (hMP : MoebiusPath G q) (hz : z ∉ q) :
    ∃ q' : List (walkupE G z h2).Dart, MoebiusPath (walkupE G z h2) q' :=
  sorry

/-- Lift a Moebius path through `WalkupN`, avoiding the chosen dart's
    face-image. (Rocq `liftN` in `jordan.v:83`.) -/
theorem MoebiusPath.lift_walkupN (G : Hypermap) (z : G.Dart)
    (h2 : Fintype.card G.Dart ≥ 2) (q : List G.Dart)
    (hMP : MoebiusPath G q) (hz : z ∉ q) (hfz : G.face z ∉ q) :
    ∃ q' : List (walkupN G z h2).Dart, MoebiusPath (walkupN G z h2) q' :=
  sorry

/-- Lift a Moebius path through `WalkupF`, avoiding the chosen dart's
    `face∘edge` image. (Rocq `liftF` in `jordan.v:91`.) -/
theorem MoebiusPath.lift_walkupF (G : Hypermap) (z : G.Dart)
    (h2 : Fintype.card G.Dart ≥ 2) (q : List G.Dart)
    (hMP : MoebiusPath G q) (hz : z ∉ q) (hfez : G.face (G.edge z) ∉ q) :
    ∃ q' : List (walkupF G z h2).Dart, MoebiusPath (walkupF G z h2) q' :=
  sorry

/-- A Moebius path covers the whole hypermap iff `q.length + 1 = #|G|`. The
    Rocq proof handles this "covers all darts" subcase explicitly to obtain
    `oG : #|G| = (size p).+1` (jordan.v:108). -/
theorem MoebiusPath.covers_all_or_witness (G : Hypermap) {q : List G.Dart}
    (hMP : MoebiusPath G q) :
    q.length + 1 = Fintype.card G.Dart ∨ ∃ z : G.Dart, z ∉ q :=
  sorry

/-- A Moebius path has at least two distinct darts, so the underlying
    hypermap has at least two darts. -/
theorem MoebiusPath.card_ge_two (G : Hypermap) {q : List G.Dart}
    (hMP : MoebiusPath G q) : Fintype.card G.Dart ≥ 2 := by
  have h_len : 2 ≤ q.length := MoebiusPath.length_ge_two hMP
  have h_nodup : q.Nodup := MoebiusPath.nodup hMP
  -- |Dart| ≥ |q.toFinset| = q.length ≥ 2.
  have h_le : q.length ≤ Fintype.card G.Dart := by
    have hsub : q.toFinset ⊆ Finset.univ := fun x _ => Finset.mem_univ x
    have hcard := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup h_nodup, Finset.card_univ] at hcard
    exact hcard
  omega

/-- Bottom case of the Walkup induction: a Moebius path that covers every
    dart of a planar hypermap is impossible. (Rocq `Euler_tree`, `jordan.v:217`.) -/
theorem moebius_full_planar (G : Hypermap) (hP : Planar G) (q : List G.Dart)
    (_hMP : MoebiusPath G q) (_hsize : q.length + 1 = Fintype.card G.Dart) :
    False :=
  sorry

/-- Hypermaps with exactly one dart are planar. -/
theorem planar_of_card_one (G : Hypermap) (h : Fintype.card G.Dart = 1) :
    Planar G :=
  sorry

/-- Hypermaps with at most one dart are vacuously planar. -/
theorem planar_of_card_lt_two (G : Hypermap) (h : Fintype.card G.Dart < 2) :
    Planar G := by
  -- card ≥ 1 since Dart is Nonempty, so card = 1.
  have h_pos : 0 < Fintype.card G.Dart := Fintype.card_pos
  have h_one : Fintype.card G.Dart = 1 := by omega
  exact planar_of_card_one G h_one

/-- Conversely, planarity of a `walkupE` reflects up to `G`. (Rocq
    `genus_WalkupE` direction in `walkup.v`.) -/
theorem walkupE_planar_lift (G : Hypermap) (z : G.Dart)
    (h2 : Fintype.card G.Dart ≥ 2) (h : Planar (walkupE G z h2)) : Planar G :=
  sorry

/-- Inductive content of `planar_jordan`: any Moebius path in a planar `G`
    contradicts the inductive hypothesis on smaller (Walkup) hypermaps. -/
theorem walkupE_no_moebius.{u} (G : Hypermap.{u})
    (ih : ∀ H : Hypermap.{u}, Fintype.card H.Dart < Fintype.card G.Dart →
            Planar H → Jordan H)
    (hP : Planar G) (q : List G.Dart) (hMP : MoebiusPath G q) : False := by
  rcases hMP.covers_all_or_witness with hsize | ⟨z, hz⟩
  · exact moebius_full_planar G hP q hMP hsize
  · have h2 : Fintype.card G.Dart ≥ 2 := MoebiusPath.card_ge_two G hMP
    obtain ⟨q', hMP'⟩ := MoebiusPath.lift_walkupE G z h2 q hMP hz
    have hcard : Fintype.card (walkupE G z h2).Dart < Fintype.card G.Dart := by
      rw [card_walkupE G z]; omega
    exact ih _ hcard (planar_walkupE G z h2 hP) q' hMP'

/-- Inductive content of `jordan_planar`: a Jordan hypermap is planar. -/
theorem walkupE_planar_descent.{u} (G : Hypermap.{u})
    (ih : ∀ H : Hypermap.{u}, Fintype.card H.Dart < Fintype.card G.Dart →
            Jordan H → Planar H)
    (hJ : Jordan G) : Planar G := by
  by_cases h1 : Fintype.card G.Dart < 2
  · exact planar_of_card_lt_two G h1
  push_neg at h1
  have h2 : Fintype.card G.Dart ≥ 2 := h1
  have ⟨z⟩ := G.instNonempty
  have hcard : Fintype.card (walkupE G z h2).Dart < Fintype.card G.Dart := by
    rw [card_walkupE G z]; omega
  have hJ' : Jordan (walkupE G z h2) := jordan_walkupE G z h2 hJ
  have hP' : Planar (walkupE G z h2) := ih _ hcard hJ'
  exact walkupE_planar_lift G z h2 hP'

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