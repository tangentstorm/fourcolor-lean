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

/-- When `f x ≠ z`, `skip1` returns `f x` directly (the else-branch). -/
theorem skip1_id_of_not_in (f : G.Dart → G.Dart) (x : G.Dart) (h : f x ≠ z) :
    skip1 G z f x = f x := by
  unfold skip1
  rw [if_neg h]

/-- When `f x = z`, `skip1` returns `f z` (the then-branch). -/
theorem skip1_of_eq (f : G.Dart → G.Dart) (x : G.Dart) (h : f x = z) :
    skip1 G z f x = f z := by
  unfold skip1
  rw [if_pos h]

/-- When f is injective and f z = z, skip1 G z f agrees with f on darts ≠ z. -/
theorem skip1_of_fixed (f : G.Dart → G.Dart) (hf : Function.Injective f)
    (hfz : f z = z) (x : G.Dart) (hx : x ≠ z) : skip1 G z f x = f x := by
  unfold skip1
  have : f x ≠ z := fun h => hx (hf (h.trans hfz.symm))
  rw [if_neg this]

/-- When `f z = z`, `skip1 G z f z = f z`. -/
theorem skip1_z_eq (f : G.Dart → G.Dart) (h : f z = z) :
    skip1 G z f z = f z := skip1_of_eq G z f z h

/-- When `f` is injective and fixes `z`, iterating `skip1 G z f` agrees with
    iterating `f` on darts `≠ z`. -/
theorem skip1_iter_id_of_fixed (f : G.Dart → G.Dart) (hf : Function.Injective f)
    (hfz : f z = z) (n : ℕ) (x : G.Dart) (hx : x ≠ z) :
    (skip1 G z f)^[n] x = f^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ, Function.comp]
    have h1 : skip1 G z f x = f x := skip1_of_fixed G z f hf hfz x hx
    rw [h1]
    have hfx_ne : f x ≠ z := by
      intro heq; exact hx (hf (heq.trans hfz.symm))
    exact ih (f x) hfx_ne

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

/-- When `G.edge z = z`, `skipEdge1` agrees with `G.edge` on all darts. -/
theorem skipEdge1_of_edge_fixed (hez : G.edge z = z) (x : G.Dart) :
    skipEdge1 G z x = G.edge x := by
  unfold skipEdge1
  rw [if_pos hez]

/-- When `G.edge z ≠ z` and `G.edge x ≠ z` and `G.face (G.edge x) ≠ z`,
    `skipEdge1 G z x = G.edge x`. -/
theorem skipEdge1_of_ne (hez : G.edge z ≠ z) (hex : G.edge x ≠ z)
    (hfex : G.face (G.edge x) ≠ z) : skipEdge1 G z x = G.edge x := by
  unfold skipEdge1
  rw [if_neg hez, if_neg hfex, if_neg hex]

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

@[simp] theorem walkupE_Dart (h2 : Fintype.card G.Dart ≥ 2) :
    (walkupE G z h2).Dart = {x : G.Dart // x ≠ z} := rfl

@[simp] theorem walkupE_edge_val (h2 : Fintype.card G.Dart ≥ 2) (x : (walkupE G z h2).Dart) :
    ((walkupE G z h2).edge x).val = skipEdge1 G z x.val := rfl

@[simp] theorem walkupE_node_val (h2 : Fintype.card G.Dart ≥ 2) (x : (walkupE G z h2).Dart) :
    ((walkupE G z h2).node x).val = skip1 G z G.node x.val := rfl

@[simp] theorem walkupE_face_val (h2 : Fintype.card G.Dart ≥ 2) (x : (walkupE G z h2).Dart) :
    ((walkupE G z h2).face x).val = skip1 G z G.face x.val := rfl

/-- When `face z = z`, walkupE.face acts as G.face on x.val (lifted). -/
theorem walkupE_face_val_of_face_fixed (h2 : Fintype.card G.Dart ≥ 2)
    (hfz : G.face z = z) (x : (walkupE G z h2).Dart) :
    ((walkupE G z h2).face x).val = G.face x.val := by
  rw [walkupE_face_val]
  exact skip1_of_fixed G z G.face face_injective hfz x.val x.property

/-- When `G.node x.val = z`, the walkupE node map yields `G.node z`
    (the skip1 then-branch). -/
theorem walkupE_node_val_of_node_eq_z (h2 : Fintype.card G.Dart ≥ 2)
    (x : (walkupE G z h2).Dart) (hnx : G.node x.val = z) :
    ((walkupE G z h2).node x).val = G.node z :=
  skip1_of_eq G z G.node x.val hnx

/-- When `node z = z`, walkupE.node acts as G.node on x.val (lifted). -/
theorem walkupE_node_val_of_node_fixed (h2 : Fintype.card G.Dart ≥ 2)
    (hnz : G.node z = z) (x : (walkupE G z h2).Dart) :
    ((walkupE G z h2).node x).val = G.node x.val := by
  rw [walkupE_node_val]
  exact skip1_of_fixed G z G.node node_injective hnz x.val x.property

/-- When `edge z = z`, walkupE.edge acts as G.edge on x.val (lifted). -/
theorem walkupE_edge_val_of_edge_fixed (h2 : Fintype.card G.Dart ≥ 2)
    (hez : G.edge z = z) (x : (walkupE G z h2).Dart) :
    ((walkupE G z h2).edge x).val = G.edge x.val := by
  rw [walkupE_edge_val]
  exact skipEdge1_of_edge_fixed G z hez x.val

/-- When `edge z ≠ z`, `edge x ≠ z`, and `face (edge x) ≠ z`,
    walkupE.edge acts as G.edge on x.val (lifted). -/
theorem walkupE_edge_val_of_ne (h2 : Fintype.card G.Dart ≥ 2)
    (hez : G.edge z ≠ z) (x : (walkupE G z h2).Dart)
    (hex : G.edge x.val ≠ z) (hfex : G.face (G.edge x.val) ≠ z) :
    ((walkupE G z h2).edge x).val = G.edge x.val := by
  rw [walkupE_edge_val]
  exact skipEdge1_of_ne G z hez hex hfex

/-- When `edge z ≠ z` and `face (edge x) = z`,
    walkupE.edge value is `G.edge z`. -/
theorem walkupE_edge_val_of_face_eq_z (h2 : Fintype.card G.Dart ≥ 2)
    (hez : G.edge z ≠ z) (x : (walkupE G z h2).Dart)
    (hfex : G.face (G.edge x.val) = z) :
    ((walkupE G z h2).edge x).val = G.edge z := by
  rw [walkupE_edge_val]
  unfold skipEdge1
  rw [if_neg hez, if_pos hfex]

/-- When `edge z ≠ z`, `face (edge x) ≠ z`, and `edge x = z`,
    walkupE.edge value is `G.edge (G.node z)`. -/
theorem walkupE_edge_val_of_edge_eq_z (h2 : Fintype.card G.Dart ≥ 2)
    (hez : G.edge z ≠ z) (x : (walkupE G z h2).Dart)
    (hfex : G.face (G.edge x.val) ≠ z)
    (hexz : G.edge x.val = z) :
    ((walkupE G z h2).edge x).val = G.edge (G.node z) := by
  rw [walkupE_edge_val]
  unfold skipEdge1
  rw [if_neg hez, if_neg hfex, if_pos hexz]

/-- The underlying value of a dart constructed via subtype literal in `walkupE` is itself. -/
@[simp] theorem walkupE_Dart_mk_val (h2 : Fintype.card G.Dart ≥ 2)
    (x : G.Dart) (hx : x ≠ z) :
    (⟨x, hx⟩ : (walkupE G z h2).Dart).val = x := rfl

theorem walkupE_Dart_eq (h2 : Fintype.card G.Dart ≥ 2) (x y : (walkupE G z h2).Dart) :
    x = y ↔ x.val = y.val := Subtype.ext_iff

@[simp] theorem walkupE_Dart_val_inj (h2 : Fintype.card G.Dart ≥ 2)
    (x y : (walkupE G z h2).Dart) :
    x.val = y.val ↔ x = y := Subtype.ext_iff.symm

/-- Every dart of `walkupE G z h2` has underlying value different from `z`. -/
theorem walkupE_dart_subtype (h2 : Fintype.card G.Dart ≥ 2) (x : (walkupE G z h2).Dart) :
    x.val ≠ z :=
  x.property

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

/-- Equivalent formulation: card G = card (walkupE G z h2) + 1. -/
theorem card_walkupE_succ (h2 : Fintype.card G.Dart ≥ 2) :
    Fintype.card G.Dart = Fintype.card (walkupE G z h2).Dart + 1 := by
  have := card_walkupE G z h2; omega

theorem card_walkupE_lt (h2 : Fintype.card G.Dart ≥ 2) :
    Fintype.card (walkupE G z h2).Dart < Fintype.card G.Dart := by
  rw [card_walkupE]; omega

/-- The predecessor relationship via Nat.add_one. -/
theorem card_walkupE_add_one (h2 : Fintype.card G.Dart ≥ 2) :
    Fintype.card (walkupE G z h2).Dart + 1 = Fintype.card G.Dart := by
  rw [card_walkupE]; omega

/-! ## Triangular identity consequences at z

These four lemmas describe how the three fixed-point conditions
edge z = z, node z = z, face z = z propagate via `edgeK`/`faceK`/`nodeK`.
They are used when case-analyzing the shape of z for `walkupE_euler_components`. -/

/-- If edge z = z and node z = z, then face z = z (from edgeK). -/
theorem face_eq_z_of_edge_node (hez : G.edge z = z) (hnz : G.node z = z) :
    G.face z = z := by
  have h := G.edgeK z
  rw [hez] at h
  exact node_injective (h.trans hnz.symm)

/-- If node z = z and face z = z, then edge z = z (from faceK). -/
theorem edge_eq_z_of_node_face (hnz : G.node z = z) (hfz : G.face z = z) :
    G.edge z = z := by
  have := G.faceK z
  rw [hfz, hnz] at this
  exact this

/-- If edge z ≠ z and node z = z, then face z ≠ z. -/
theorem face_ne_z_of_edge_ne_node_eq (hez : G.edge z ≠ z) (hnz : G.node z = z) :
    G.face z ≠ z := by
  intro hfz
  exact hez (edge_eq_z_of_node_face G z hnz hfz)

/-- If node z ≠ z and face z = z, then edge z ≠ z. -/
theorem edge_ne_z_of_node_ne_face_eq (hnz : G.node z ≠ z) (hfz : G.face z = z) :
    G.edge z ≠ z := by
  intro hez
  have := G.edgeK z
  rw [hez, hfz] at this
  exact hnz this

/-- `node z = z ∧ face z = z` implies `edge z = z`. -/
theorem all_fixed_at_z (hez : G.edge z = z) (hnz : G.node z = z) :
    G.face z = z := face_eq_z_of_edge_node G z hez hnz

/-- All three at z fixed: edge, node, face. -/
theorem all_three_fixed_iff (G : Hypermap) (z : G.Dart) :
    (G.edge z = z ∧ G.node z = z) ↔ (G.edge z = z ∧ G.node z = z ∧ G.face z = z) := by
  constructor
  · rintro ⟨he, hn⟩
    exact ⟨he, hn, face_eq_z_of_edge_node G z he hn⟩
  · rintro ⟨he, hn, _⟩
    exact ⟨he, hn⟩

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