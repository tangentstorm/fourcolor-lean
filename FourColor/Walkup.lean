/-
Copyright (c) 2006-2018 Microsoft Corporation and Inria (Coq version).
Lean 4 port of the Four Color Theorem formalization.

The Walkup construction removes a point from a hypermap's domain,
suppressing it from two of the three permutations. The third permutation
then needs a slightly more complex adjustment to reestablish the
triangular identity.

There are three variants (WalkupE, WalkupN, WalkupF) corresponding to
which permutation gets the complex adjustment. All three are used in the
proof: WalkupE in cube.v, WalkupN in kempe.v, and WalkupF in contract.v.

In the Coq formalization:
  WalkupE uses skip_edge (special), skip(node), skip(face)
  WalkupN = WalkupE (mirror G) z
  WalkupF = WalkupE (dual G) z
-/
import FourColor.Hypermap

set_option maxHeartbeats 1600000

open Hypermap

namespace Hypermap

variable (G : Hypermap) (z : G.Dart)

/-! ## The skip construction -/

/-- Given a function f on Dart and a dart z to remove,
    construct a function that "skips" over z.
    If f(x) = z, return f(z) instead (collapsing the orbit). -/
noncomputable def skip1 (f : G.Dart → G.Dart) (x : G.Dart) : G.Dart :=
  if f x = z then f z else f x

/-- skip1 preserves the property of being ≠ z, when f is injective and x ≠ z. -/
theorem skip1_ne (f : G.Dart → G.Dart) (hf : Function.Injective f)
    (x : G.Dart) (hx : x ≠ z) : skip1 G z f x ≠ z := by
  unfold skip1
  split
  · rename_i hfx
    intro hfz
    exact hx (hf (hfx.trans hfz.symm))
  · assumption

/-! ## The special skip_edge function -/

/-- The special edge skip function for WalkupE.
    Unlike skip1, this function has three cases to ensure the triangular
    identity is preserved when combined with skip1 for node and face.

    Matches the Coq definition:
    skip_edge1 x :=
      if ez = z then edge x
      else if face (edge x) = z then ez
      else if edge x = z then edge (node z)
      else edge x -/
noncomputable def skipEdge1 (x : G.Dart) : G.Dart :=
  if G.edge z = z then G.edge x
  else if G.face (G.edge x) = z then G.edge z
  else if G.edge x = z then G.edge (G.node z)
  else G.edge x

/-- skipEdge1 maps darts ≠ z to darts ≠ z. -/
theorem skipEdge1_ne (x : G.Dart) (hx : x ≠ z) : skipEdge1 G z x ≠ z := by
  unfold skipEdge1
  split_ifs with h1 h2 h3
  · intro h; exact hx (edge_injective (h.trans h1.symm))
  · exact h1
  · intro henz
    have hfz : G.face z = z := by
      have := nodeK (z : G.Dart); rw [henz] at this; exact this
    exact h2 (by rw [h3, hfz])
  · exact h3

/-! ## Walkup transforms -/

noncomputable def walkupE (h2 : Fintype.card G.Dart ≥ 2) : Hypermap where
  Dart := {x : G.Dart // x ≠ z}
  instFintype := Subtype.fintype _
  instDecEq := inferInstance
  instNonempty := by
    rw [← Fintype.card_pos_iff]
    simp only [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton]
    omega
  edge := fun ⟨x, hx⟩ => ⟨skipEdge1 G z x, skipEdge1_ne G z x hx⟩
  node := fun ⟨x, hx⟩ => ⟨skip1 G z G.node x, skip1_ne G z G.node node_injective x hx⟩
  face := fun ⟨x, hx⟩ => ⟨skip1 G z G.face x, skip1_ne G z G.face face_injective x hx⟩
  edgeK := by
    simp +zetaDelta at *;
    intro a ha
    by_cases hz : G.edge z = z;
    all_goals unfold Hypermap.skipEdge1; simp_all +decide [ Hypermap.skip1 ];
    all_goals have := G.edgeK a; have := G.faceK a; have := G.nodeK a; split_ifs at * <;> simp_all +decide [ Function.Injective.eq_iff G.edge_injective, Function.Injective.eq_iff G.node_injective, Function.Injective.eq_iff G.face_injective ] ;
    all_goals have := G.edgeK z; have := G.faceK z; have := G.nodeK z; simp_all +decide [ Function.Injective.eq_iff G.edge_injective, Function.Injective.eq_iff G.node_injective, Function.Injective.eq_iff G.face_injective ] ;

/-- WalkupN: remove z, adjusting the node permutation specially. -/
noncomputable def walkupN (h2 : Fintype.card G.Dart ≥ 2) : Hypermap :=
  walkupE (mirror G) z (by simp [mirror]; exact h2)

/-- WalkupF: remove z, adjusting the face permutation specially. -/
noncomputable def walkupF (h2 : Fintype.card G.Dart ≥ 2) : Hypermap :=
  walkupE (dual G) z (by simp [dual]; exact h2)

/-! ## Key Walkup properties -/

/-- The cardinality of a Walkup map is one less than the original. -/
theorem card_walkupE (h2 : Fintype.card G.Dart ≥ 2) :
    Fintype.card (walkupE G z h2).Dart = Fintype.card G.Dart - 1 := by
  simp only [walkupE]
  rw [Fintype.card_subtype_compl, Fintype.card_ofSubsingleton]

/-! ## Euler formula changes under WalkupE -/

/-- The Euler formula components change in a controlled way under WalkupE.
    There exist natural numbers a ≥ b such that:
    - 2a + eulerLhs(G') = eulerLhs(G) + 1
    - 2b + eulerRhs(G') = eulerRhs(G) + 1

    The values of a and b depend on whether z has a self-loop (glink z z),
    whether z and node(z) are edge-connected (cross_edge), and whether
    removing z disconnects the glink component.

    Corresponds to Euler_lhs_WalkupE and Euler_rhs_WalkupE in Coq's walkup.v. -/
theorem walkupE_euler_components (h2 : Fintype.card G.Dart ≥ 2) :
    ∃ a b : ℕ, a ≥ b ∧
      2 * a + eulerLhs (walkupE G z h2) = eulerLhs G + 1 ∧
      2 * b + eulerRhs (walkupE G z h2) = eulerRhs G + 1 := by
  sorry

/-! ## Genus monotonicity and even genus -/

/-
The genus does not increase when removing a dart via WalkupE.
    Follows from the Euler component changes: genus G' ≤ genus G.
-/
theorem le_genus_WalkupE (h2 : Fintype.card G.Dart ≥ 2) :
    genus (walkupE G z h2) ≤ genus G := by
  obtain ⟨a, b, hab, hlhs, hrhs⟩ := walkupE_euler_components G z h2
  unfold genus
  -- From hlhs: eulerLhs G' = eulerLhs G + 1 - 2a
  -- From hrhs: eulerRhs G' = eulerRhs G + 1 - 2b
  -- With a ≥ b:
  -- (eulerLhs G' - eulerRhs G')/2
  -- = (eulerLhs G + 1 - 2a - eulerRhs G - 1 + 2b)/2
  -- = (eulerLhs G - eulerRhs G - 2(a-b))/2
  -- ≤ (eulerLhs G - eulerRhs G)/2
  omega

/-
The even genus property is preserved from WalkupE to G.
    If G' has even genus, then G has even genus.
-/
theorem even_genus_WalkupE (h2 : Fintype.card G.Dart ≥ 2) :
    eulerLhs (walkupE G z h2) = 2 * genus (walkupE G z h2) + eulerRhs (walkupE G z h2) →
    eulerLhs G = 2 * genus G + eulerRhs G := by
  obtain ⟨a, b, hab, hlhs, hrhs⟩ := walkupE_euler_components G z h2
  -- From hlhs: 2a + Lhs' = Lhs + 1
  -- From hrhs: 2b + Rhs' = Rhs + 1
  -- Assume: Lhs' = 2*genus' + Rhs' (even genus for G')
  -- Then: Lhs + 1 = 2a + 2*genus' + Rhs' = 2a + 2*genus' + Rhs + 1 - 2b
  -- So: Lhs = 2(a - b + genus') + Rhs
  -- And genus G = (Lhs - Rhs)/2 = a - b + genus'
  -- So: Lhs = 2*(a - b + genus') + Rhs = 2*genus G + Rhs ✓
  unfold Hypermap.genus;
  omega

/-! ## Planarity and Jordan preservation -/

/-- The Euler planarity condition is preserved by WalkupE.
    Follows from le_genus_WalkupE: if genus G = 0 and genus G' ≤ genus G,
    then genus G' = 0. -/
theorem planar_walkupE (h2 : Fintype.card G.Dart ≥ 2) (hP : Planar G) :
    Planar (walkupE G z h2) := by
  unfold Planar at *
  have hle := le_genus_WalkupE G z h2
  omega

/-- The Jordan property is preserved by all Walkup transforms.
    Corresponds to `Jordan_WalkupE` in Coq's walkup.v (~170 lines).
    The proof lifts Moebius paths from WalkupE back to G. -/
theorem jordan_walkupE (h2 : Fintype.card G.Dart ≥ 2) (hJ : Jordan G) :
    Jordan (walkupE G z h2) := by
  sorry

end Hypermap