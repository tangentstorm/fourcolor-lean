/-
Copyright (c) 2006-2018 Microsoft Corporation and Inria (Coq version).
Lean 4 port of the Four Color Theorem formalization.

A (finite) hypermap is a triplet of permutations (edge, node, face) over a
finite type satisfying the triangular identity: node ∘ face ∘ edge = id.
This is equivalent to an arbitrary pair of permutations, but the three-function
presentation better supports symmetries.
-/
import Mathlib

set_option maxHeartbeats 800000

open Finset Function Equiv.Perm

universe u

/-! ## Hypermap Definition -/

/-- A finite hypermap: a finite type with three permutations edge, node, face
    satisfying the triangular identity `node (face (edge x)) = x` for all x. -/
structure Hypermap where
  /-- The type of darts -/
  Dart : Type u
  [instFintype : Fintype Dart]
  [instDecEq : DecidableEq Dart]
  [instNonempty : Nonempty Dart]
  /-- The edge permutation -/
  edge : Dart → Dart
  /-- The node permutation -/
  node : Dart → Dart
  /-- The face permutation -/
  face : Dart → Dart
  /-- The triangular identity: node ∘ face ∘ edge = id -/
  edgeK : ∀ x, node (face (edge x)) = x

attribute [instance] Hypermap.instFintype Hypermap.instDecEq Hypermap.instNonempty

namespace Hypermap

variable {G : Hypermap}

/-! ## Basic cancellation and injectivity lemmas -/

@[simp]
theorem edgeK' (x : G.Dart) : G.node (G.face (G.edge x)) = x := G.edgeK x

theorem faceK (x : G.Dart) : G.edge (G.node (G.face x)) = x := by
  have h := G.edgeK (G.node (G.face x))
  have h_inj : Function.Injective (G.node ∘ G.face) := by
    exact Finite.injective_iff_surjective.mpr (fun y => ⟨G.edge y, by simp +decide [G.edgeK]⟩)
  exact h_inj h

theorem nodeK (x : G.Dart) : G.face (G.edge (G.node x)) = x := by
  have h1 : G.node (G.face (G.edge (G.node x))) = G.node x := by exact edgeK' (G.node x)
  have h_node_inj : Function.Injective G.node := by
    exact Finite.injective_iff_surjective.mpr (fun x => by exact ⟨_, G.edgeK x⟩)
  exact h_node_inj h1

theorem edge_injective : Function.Injective G.edge := by
  intro x y h
  have hx := G.edgeK x
  have hy := G.edgeK y
  rw [h] at hx
  exact hx.symm.trans hy

theorem node_injective : Function.Injective G.node := by
  intro x y hxy
  have h_surj : Function.Surjective G.node := fun x => ⟨_, G.edgeK x⟩
  exact Finite.injective_iff_surjective.mpr h_surj hxy

theorem face_injective : Function.Injective G.face := by
  intros x y hxy
  rw [← G.faceK x, ← G.faceK y, hxy]

theorem edge_surjective : Function.Surjective G.edge := by
  intro y; exact ⟨G.node (G.face y), by exact faceK y⟩

theorem node_surjective : Function.Surjective G.node := by
  intro y; exact ⟨G.face (G.edge y), by exact edgeK' y⟩

theorem face_surjective : Function.Surjective G.face := by
  intro y; exact ⟨G.edge (G.node y), by exact nodeK y⟩

theorem edge_bijective : Function.Bijective G.edge :=
  ⟨edge_injective, edge_surjective⟩

theorem node_bijective : Function.Bijective G.node :=
  ⟨node_injective, node_surjective⟩

theorem face_bijective : Function.Bijective G.face :=
  ⟨face_injective, face_surjective⟩

/-- The edge permutation as an `Equiv.Perm`. -/
noncomputable def edgePerm (G : Hypermap) : Equiv.Perm G.Dart :=
  Equiv.ofBijective G.edge edge_bijective

/-- The node permutation as an `Equiv.Perm`. -/
noncomputable def nodePerm (G : Hypermap) : Equiv.Perm G.Dart :=
  Equiv.ofBijective G.node node_bijective

/-- The face permutation as an `Equiv.Perm`. -/
noncomputable def facePerm (G : Hypermap) : Equiv.Perm G.Dart :=
  Equiv.ofBijective G.face face_bijective

/-! ## Connectivity relations -/

/-- Two darts are edge-connected if one is reachable from the other by
    iterating the edge permutation. -/
def cedge (G : Hypermap) (x y : G.Dart) : Prop :=
  ∃ n : ℕ, G.edge^[n] x = y

/-- Two darts are node-connected if one is reachable from the other by
    iterating the node permutation. -/
def cnode (G : Hypermap) (x y : G.Dart) : Prop :=
  ∃ n : ℕ, G.node^[n] x = y

/-- Two darts are face-connected if one is reachable from the other by
    iterating the face permutation. -/
def cface (G : Hypermap) (x y : G.Dart) : Prop :=
  ∃ n : ℕ, G.face^[n] x = y

/-! ## Graph links -/

/-- The glink relation: y is an image of x under edge, node, or face. -/
def glink (G : Hypermap) (x y : G.Dart) : Prop :=
  G.edge x = y ∨ G.node x = y ∨ G.face x = y

/-- The clink relation: either x = node y or face x = y.
    Used for defining paths (contours) in the hypermap. -/
def clink (G : Hypermap) (x y : G.Dart) : Prop :=
  x = G.node y ∨ G.face x = y

/-- Two darts are in the same component if connected by a sequence of glinks. -/
def gcomp (G : Hypermap) (x y : G.Dart) : Prop :=
  Relation.ReflTransGen (glink G) x y

/-- A hypermap is connected if all darts are in the same glink component. -/
def Connected (G : Hypermap) : Prop :=
  ∀ x y : G.Dart, gcomp G x y

/-! ## Euler formula and genus -/

/-- The equivalence closure of glink, used for counting connected components. -/
noncomputable instance glinkSetoid (G : Hypermap) : Setoid G.Dart where
  r := Relation.EqvGen (glink G)
  iseqv := Relation.EqvGen.is_equivalence _

/-- Number of orbits of a permutation, counting fixed points as 1-orbits. -/
noncomputable def numOrbits (σ : Equiv.Perm G.Dart) : ℕ :=
  σ.cycleFactorsFinset.card + (Fintype.card G.Dart - σ.support.card)

/-- Number of edge orbits. -/
noncomputable def fcardEdge (G : Hypermap) : ℕ :=
  numOrbits G.edgePerm

/-- Number of node orbits. -/
noncomputable def fcardNode (G : Hypermap) : ℕ :=
  numOrbits G.nodePerm

/-- Number of face orbits. -/
noncomputable def fcardFace (G : Hypermap) : ℕ :=
  numOrbits G.facePerm

/-- The number of glink-connected components. -/
noncomputable def nComp (G : Hypermap) : ℕ := by
  haveI : DecidableRel (glinkSetoid G).r := Classical.decRel _
  exact Fintype.card (Quotient (glinkSetoid G))

/-- Left-hand side of the Euler formula: 2 * nComp + |Dart|. -/
noncomputable def eulerLhs (G : Hypermap) : ℕ :=
  2 * nComp G + Fintype.card G.Dart

/-- Right-hand side of the Euler formula: #edges + #nodes + #faces. -/
noncomputable def eulerRhs (G : Hypermap) : ℕ :=
  fcardEdge G + fcardNode G + fcardFace G

/-- The genus of a hypermap. -/
noncomputable def genus (G : Hypermap) : ℕ :=
  (eulerLhs G - eulerRhs G) / 2

/-- A hypermap is planar if it has genus 0. -/
def Planar (G : Hypermap) : Prop :=
  genus G = 0

/-! ## The Jordan property -/

/-- Two darts are clink-connected: reachable by iterating clink steps. -/
def cconnect (G : Hypermap) (x y : G.Dart) : Prop :=
  Relation.ReflTransGen (clink G) x y

/-- `List.mem2 p a b` holds when `a` appears strictly before `b` in `p`,
    i.e., there exist indices `i < j` with `p[i] = a` and `p[j] = b`.
    This mirrors the Coq/ssreflect `mem2` from `seq.v`:
      `mem2 s x y := y \in drop (index x s).+1 s`. -/
def List.mem2 {α : Type*} (p : List α) (a b : α) : Prop :=
  ∃ i j, i < j ∧ j < p.length ∧ p[i]? = some a ∧ p[j]? = some b

/-- The inverse of the node permutation. Corresponds to `finv node` in the
    Coq formalization. -/
noncomputable def finvNode (G : Hypermap) : G.Dart → G.Dart :=
  G.nodePerm.symm

theorem finvNode_node (x : G.Dart) : G.finvNode (G.node x) = x :=
  Equiv.ofBijective_symm_apply_apply G.node node_bijective x

theorem node_finvNode (x : G.Dart) : G.node (G.finvNode x) = x :=
  Equiv.ofBijective_apply_symm_apply G.node node_bijective x

/-- The inverse of the edge permutation. -/
noncomputable def finvEdge (G : Hypermap) : G.Dart → G.Dart :=
  G.edgePerm.symm

theorem finvEdge_edge (x : G.Dart) : G.finvEdge (G.edge x) = x :=
  Equiv.ofBijective_symm_apply_apply G.edge edge_bijective x

theorem edge_finvEdge (x : G.Dart) : G.edge (G.finvEdge x) = x :=
  Equiv.ofBijective_apply_symm_apply G.edge edge_bijective x

/-- The inverse of the face permutation. -/
noncomputable def finvFace (G : Hypermap) : G.Dart → G.Dart :=
  G.facePerm.symm

theorem finvFace_face (x : G.Dart) : G.finvFace (G.face x) = x :=
  Equiv.ofBijective_symm_apply_apply G.face face_bijective x

theorem face_finvFace (x : G.Dart) : G.face (G.finvFace x) = x :=
  Equiv.ofBijective_apply_symm_apply G.face face_bijective x

/-- A Moebius path in a hypermap.

    Corresponds to `Moebius_path` in the Coq formalization (hypermap.v:260):

      Definition Moebius_path q :=
        if q isn't x :: p then false else
        [&& uniq q, path clink x p & mem2 p (finv node (last x p)) (node x)].

    That is, `q = x :: p` where:
    - `q` has no duplicates (`uniq q` ↔ `q.Nodup`),
    - `p` is a clink-path starting from `x` (`path clink x p` ↔ `List.Chain (clink G) x p`),
    - `p` contains both `finv node (last x p)` and `node x`, with the former
      appearing strictly before the latter (`mem2`). This "twist" on the
      node-links at the endpoints detects a topological non-orientability.

    A hypermap has the Jordan property iff it contains no Moebius paths. -/
def MoebiusPath (G : Hypermap) (q : List G.Dart) : Prop :=
  match q with
  | [] => False
  | x :: p =>
    (x :: p).Nodup ∧
    List.IsChain (clink G) (x :: p) ∧
    List.mem2 p (G.finvNode ((x :: p).getLast (by simp))) (G.node x)

/-- The Jordan property: a hypermap has no Moebius paths. -/
def Jordan (G : Hypermap) : Prop :=
  ∀ q : List G.Dart, ¬ MoebiusPath G q

/-! ## Derived maps -/

/-- The dual hypermap: invert all permutations, swap node and face. -/
noncomputable def dual (G : Hypermap) : Hypermap where
  Dart := G.Dart
  edge := Function.invFun G.edge
  node := Function.invFun G.face
  face := Function.invFun G.node
  edgeK := fun x => by
    -- The goal is `invFun G.face (invFun G.node (invFun G.edge x)) = x`.
    -- Let w abbreviate the LHS. Applying face/node/edge successively and
    -- using `Function.rightInverse_invFun` on surjective permutations
    -- yields `edge (node (face w)) = x`. But `faceK` says
    -- `edge (node (face w)) = w`, so `w = x`.
    set w := Function.invFun G.face (Function.invFun G.node (Function.invFun G.edge x))
    have hE := Function.rightInverse_invFun G.edge_surjective
    have hN := Function.rightInverse_invFun G.node_surjective
    have hF := Function.rightInverse_invFun G.face_surjective
    have h1 : G.edge (G.node (G.face w)) = x := by
      show G.edge (G.node (G.face w)) = x
      rw [show G.face w = Function.invFun G.node (Function.invFun G.edge x) from hF _,
          show G.node (Function.invFun G.node (Function.invFun G.edge x)) =
            Function.invFun G.edge x from hN _,
          hE]
    rw [faceK] at h1
    exact h1

/-- The mirror hypermap. -/
noncomputable def mirror (G : Hypermap) : Hypermap where
  Dart := G.Dart
  edge := G.face ∘ G.node
  node := Function.invFun G.node
  face := Function.invFun G.face
  edgeK := by
    intro x
    convert Function.leftInverse_invFun G.node_bijective.injective _ using 1
    exact congr_arg _ (Function.leftInverse_invFun G.face_bijective.injective _)

/-! ## Symmetry / equivalence lemmas for glink, gcomp, clink, cconnect -/

-- Coq: hypermap.v (gcomp reflexivity)
theorem gcomp_refl (G : Hypermap) (x : G.Dart) : gcomp G x x :=
  Relation.ReflTransGen.refl

-- Coq: hypermap.v (gcomp transitivity)
theorem gcomp_trans (G : Hypermap) : Transitive (gcomp G) :=
  fun _ _ _ => Relation.ReflTransGen.trans

/-- Reversing a single glink step yields a two-step gcomp path, using the
    triangular identity to express the inverse. -/
private theorem glink_reverse_gcomp {x y : G.Dart} (h : glink G x y) :
    gcomp G y x := by
  rcases h with he | hn | hf
  · -- edge x = y ⟹ y →(face) face y →(node) node(face(edge x)) = x
    subst he
    exact Relation.ReflTransGen.head (Or.inr (Or.inr rfl))
      (Relation.ReflTransGen.single (Or.inr (Or.inl (G.edgeK x))))
  · -- node x = y ⟹ y →(edge) edge y →(face) face(edge(node x)) = x
    subst hn
    exact Relation.ReflTransGen.head (Or.inl rfl)
      (Relation.ReflTransGen.single (Or.inr (Or.inr (G.nodeK x))))
  · -- face x = y ⟹ y →(node) node y →(edge) edge(node(face x)) = x
    subst hf
    exact Relation.ReflTransGen.head (Or.inr (Or.inl rfl))
      (Relation.ReflTransGen.single (Or.inl (G.faceK x)))

-- Coq: hypermap.v (gcomp symmetry)
theorem gcomp_symm {x y : G.Dart} (h : gcomp G x y) : gcomp G y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact (glink_reverse_gcomp hstep).trans ih

/-- Every clink step can be realized as a gcomp path (1 or 2 glink steps). -/
-- Coq: hypermap.v (clink ⊂ gcomp)
theorem clink_gcomp {x y : G.Dart} (h : clink G x y) : gcomp G x y := by
  rcases h with hn | hf
  · -- x = node y ⟹ x →(edge) edge x →(face) face(edge(node y)) = y
    subst hn
    exact Relation.ReflTransGen.head (Or.inl rfl)
      (Relation.ReflTransGen.single (Or.inr (Or.inr (G.nodeK y))))
  · -- face x = y ⟹ direct glink face step
    exact Relation.ReflTransGen.single (Or.inr (Or.inr hf))

-- Coq: hypermap.v (cconnect ⊂ gcomp)
theorem cconnect_gcomp {x y : G.Dart} (h : cconnect G x y) : gcomp G x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.trans (clink_gcomp hstep)

-- TODO: cconnect_symm — reversing a single clink step requires iterating
-- around finite permutation orbits (face-forward or node-backward), which
-- needs the order-of-permutation machinery. Left for a future PR.

/-! ## Key planarity theorems -/

-- The even genus property (even_genusP) and Euler inequality (euler_le)
-- are proved in Jordan.lean via Walkup induction.
-- They are available as Hypermap.even_genusP and Hypermap.euler_le
-- after importing FourColor.Jordan.

end Hypermap