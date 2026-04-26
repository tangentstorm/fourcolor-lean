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

theorem edge_inj_iff (G : Hypermap) {x y : G.Dart} : G.edge x = G.edge y ↔ x = y :=
  ⟨fun h => G.edge_injective h, fun h => by rw [h]⟩

theorem node_inj_iff (G : Hypermap) {x y : G.Dart} : G.node x = G.node y ↔ x = y :=
  ⟨fun h => G.node_injective h, fun h => by rw [h]⟩

theorem face_inj_iff (G : Hypermap) {x y : G.Dart} : G.face x = G.face y ↔ x = y :=
  ⟨fun h => G.face_injective h, fun h => by rw [h]⟩

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

/-! ## Dot-syntax projections for Connected and glink -/

theorem Connected.all_gcomp {G : Hypermap} (h : Connected G) (x y : G.Dart) :
    gcomp G x y :=
  h x y

theorem glink.edge (G : Hypermap) (x : G.Dart) : glink G x (G.edge x) :=
  Or.inl rfl

theorem glink.node (G : Hypermap) (x : G.Dart) : glink G x (G.node x) :=
  Or.inr (Or.inl rfl)

theorem glink.face (G : Hypermap) (x : G.Dart) : glink G x (G.face x) :=
  Or.inr (Or.inr rfl)

theorem gcomp.refl (G : Hypermap) (x : G.Dart) : gcomp G x x :=
  Relation.ReflTransGen.refl

theorem gcomp.trans {G : Hypermap} {x y z : G.Dart}
    (h1 : gcomp G x y) (h2 : gcomp G y z) : gcomp G x z :=
  Relation.ReflTransGen.trans h1 h2

theorem gcomp.edge (G : Hypermap) (x : G.Dart) : gcomp G x (G.edge x) :=
  Relation.ReflTransGen.single (glink.edge G x)

theorem gcomp.node (G : Hypermap) (x : G.Dart) : gcomp G x (G.node x) :=
  Relation.ReflTransGen.single (glink.node G x)

theorem gcomp.face (G : Hypermap) (x : G.Dart) : gcomp G x (G.face x) :=
  Relation.ReflTransGen.single (glink.face G x)

/-- Any cedge-related dart is gcomp-related. -/
theorem cedge_imp_gcomp {G : Hypermap} {x y : G.Dart} (h : cedge G x y) : gcomp G x y := by
  obtain ⟨n, rfl⟩ := h
  induction n with
  | zero => exact gcomp.refl G x
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact gcomp.trans ih (gcomp.edge G _)

/-- Any cnode-related dart is gcomp-related. -/
theorem cnode_imp_gcomp {G : Hypermap} {x y : G.Dart} (h : cnode G x y) : gcomp G x y := by
  obtain ⟨n, rfl⟩ := h
  induction n with
  | zero => exact gcomp.refl G x
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact gcomp.trans ih (gcomp.node G _)

/-- Any cface-related dart is gcomp-related. -/
theorem cface_imp_gcomp {G : Hypermap} {x y : G.Dart} (h : cface G x y) : gcomp G x y := by
  obtain ⟨n, rfl⟩ := h
  induction n with
  | zero => exact gcomp.refl G x
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact gcomp.trans ih (gcomp.face G _)

/-- A Connected hypermap relates any two darts via gcomp from cedge. -/
theorem Connected.gcomp_of_any {G : Hypermap} (h : Connected G) (x y : G.Dart) : gcomp G x y :=
  h x y

/-- A Connected hypermap relates dart x to its edge image. -/
theorem Connected.gcomp_edge {G : Hypermap} (h : Connected G) (x : G.Dart) :
    gcomp G x (G.edge x) := h x (G.edge x)

/-- A Connected hypermap relates dart x to its node image. -/
theorem Connected.gcomp_node {G : Hypermap} (h : Connected G) (x : G.Dart) :
    gcomp G x (G.node x) := h x (G.node x)

/-- A Connected hypermap relates dart x to its face image. -/
theorem Connected.gcomp_face {G : Hypermap} (h : Connected G) (x : G.Dart) :
    gcomp G x (G.face x) := h x (G.face x)

/-- The empty hypermap (1 dart) is trivially Connected. -/
theorem Connected.of_card_one (G : Hypermap) (h1 : Fintype.card G.Dart = 1) :
    Connected G := by
  intro x y
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp h1
  have hx : x = a := ha x
  have hy : y = a := ha y
  rw [hx, hy]
  exact gcomp.refl G a

/-- glink applied via cedge: a single edge step is a glink. -/
theorem glink_of_cedge_step {G : Hypermap} (x : G.Dart) : glink G x (G.edge x) :=
  glink.edge G x

/-- glink applied via cnode: a single node step is a glink. -/
theorem glink_of_cnode_step {G : Hypermap} (x : G.Dart) : glink G x (G.node x) :=
  glink.node G x

/-- glink applied via cface: a single face step is a glink. -/
theorem glink_of_cface_step {G : Hypermap} (x : G.Dart) : glink G x (G.face x) :=
  glink.face G x

/-- An iterated edge step is a gcomp. -/
theorem gcomp_iter_edge (G : Hypermap) (n : ℕ) (x : G.Dart) :
    gcomp G x (G.edge^[n] x) :=
  cedge_imp_gcomp ⟨n, rfl⟩

/-- An iterated node step is a gcomp. -/
theorem gcomp_iter_node (G : Hypermap) (n : ℕ) (x : G.Dart) :
    gcomp G x (G.node^[n] x) :=
  cnode_imp_gcomp ⟨n, rfl⟩

/-- An iterated face step is a gcomp. -/
theorem gcomp_iter_face (G : Hypermap) (n : ℕ) (x : G.Dart) :
    gcomp G x (G.face^[n] x) :=
  cface_imp_gcomp ⟨n, rfl⟩

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

namespace List.mem2

/-- `mem2` on an empty list is always false. -/
theorem not_nil {α : Type*} (a b : α) : ¬ List.mem2 ([] : List α) a b := by
  rintro ⟨i, j, _, hj, _, _⟩
  simp at hj

/-- `mem2 p a b` requires both `a` and `b` to be in `p`. -/
theorem mem_left {α : Type*} {p : List α} {a b : α}
    (h : List.mem2 p a b) : a ∈ p := by
  obtain ⟨i, j, hij, hj, ha, _⟩ := h
  have hi : i < p.length := by omega
  have heq : p[i] = a := Option.some.inj (by rw [← List.getElem?_eq_getElem hi]; exact ha)
  exact heq ▸ List.getElem_mem hi

theorem mem_right {α : Type*} {p : List α} {a b : α}
    (h : List.mem2 p a b) : b ∈ p := by
  obtain ⟨i, j, _, hj, _, hb⟩ := h
  have heq : p[j] = b := Option.some.inj (by rw [← List.getElem?_eq_getElem hj]; exact hb)
  exact heq ▸ List.getElem_mem hj

end List.mem2

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

/-- `finvNode` is injective. -/
theorem finvNode_injective (G : Hypermap) : Function.Injective G.finvNode := by
  intro x y h
  rw [← node_finvNode (x := x), ← node_finvNode (x := y), h]

/-- `finvEdge` is injective. -/
theorem finvEdge_injective (G : Hypermap) : Function.Injective G.finvEdge := by
  intro x y h
  rw [← edge_finvEdge (x := x), ← edge_finvEdge (x := y), h]

/-- `finvFace` is injective. -/
theorem finvFace_injective (G : Hypermap) : Function.Injective G.finvFace := by
  intro x y h
  rw [← face_finvFace (x := x), ← face_finvFace (x := y), h]

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

/-- A Moebius path is never empty. -/
theorem MoebiusPath.ne_nil {G : Hypermap} {q : List G.Dart}
    (h : MoebiusPath G q) : q ≠ [] := by
  intro hq; rw [hq] at h; exact h

/-- `MoebiusPath G []` is vacuously false. -/
theorem not_MoebiusPath_nil (G : Hypermap) :
    ¬ MoebiusPath G ([] : List G.Dart) := fun h => h

/-- A Moebius path has at least 2 darts: the head `x` and enough elements
    in the tail `p` to support the `mem2` twist. -/
theorem MoebiusPath.length_ge_two {G : Hypermap} {q : List G.Dart}
    (h : MoebiusPath G q) : 2 ≤ q.length := by
  match q, h with
  | x :: p, ⟨_, _, hmem2⟩ =>
    -- mem2 requires some j < p.length, so p is nonempty, so (x :: p).length ≥ 2.
    obtain ⟨_, j, _, hj, _, _⟩ := hmem2
    have : 0 < p.length := by omega
    simp [List.length_cons]; omega

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

/-! ## Structural simp lemmas for dual and mirror

These unfold the fields of `dual` and `mirror` by definitional reduction.
Corresponds to projections used implicitly throughout `hypermap.v` and `geometry.v`
in the Coq formalization. -/

/-- `(dual G).Dart` is definitionally equal to `G.Dart`. (hypermap.v) -/
@[simp] theorem dual_Dart (G : Hypermap) : (dual G).Dart = G.Dart := rfl

/-- `(mirror G).Dart` is definitionally equal to `G.Dart`. (hypermap.v) -/
@[simp] theorem mirror_Dart (G : Hypermap) : (mirror G).Dart = G.Dart := rfl

/-- The cardinality of darts is invariant under `dual`. (hypermap.v) -/
@[simp] theorem card_dual (G : Hypermap) :
    Fintype.card (dual G).Dart = Fintype.card G.Dart := rfl

/-- The cardinality of darts is invariant under `mirror`. (hypermap.v) -/
@[simp] theorem card_mirror (G : Hypermap) :
    Fintype.card (mirror G).Dart = Fintype.card G.Dart := rfl

/-- The edge of the dual is the inverse of the original edge. (hypermap.v) -/
@[simp] theorem dual_edge (G : Hypermap) : (dual G).edge = Function.invFun G.edge := rfl

/-- The node of the dual is the inverse of the original face. (hypermap.v) -/
@[simp] theorem dual_node (G : Hypermap) : (dual G).node = Function.invFun G.face := rfl

/-- The face of the dual is the inverse of the original node. (hypermap.v) -/
@[simp] theorem dual_face (G : Hypermap) : (dual G).face = Function.invFun G.node := rfl

/-- Composition of dual edge with original edge yields identity (left-invFun). -/
theorem dual_edge_apply (G : Hypermap) (x : G.Dart) :
    G.edge ((dual G).edge x) = x :=
  Function.rightInverse_invFun G.edge_surjective x

/-- Composition of dual node with original face yields identity. -/
theorem dual_node_apply (G : Hypermap) (x : G.Dart) :
    G.face ((dual G).node x) = x :=
  Function.rightInverse_invFun G.face_surjective x

/-- Composition of dual face with original node yields identity. -/
theorem dual_face_apply (G : Hypermap) (x : G.Dart) :
    G.node ((dual G).face x) = x :=
  Function.rightInverse_invFun G.node_surjective x

/-- The edge of the mirror is `face ∘ node`. (hypermap.v) -/
@[simp] theorem mirror_edge (G : Hypermap) : (mirror G).edge = G.face ∘ G.node := rfl

/-- The node of the mirror is the inverse of the original node. (hypermap.v) -/
@[simp] theorem mirror_node (G : Hypermap) : (mirror G).node = Function.invFun G.node := rfl

/-- The face of the mirror is the inverse of the original face. (hypermap.v) -/
@[simp] theorem mirror_face (G : Hypermap) : (mirror G).face = Function.invFun G.face := rfl

/-- Composition of mirror node with original node yields identity. -/
theorem mirror_node_apply (G : Hypermap) (x : G.Dart) :
    G.node ((mirror G).node x) = x :=
  Function.rightInverse_invFun G.node_surjective x

/-- Composition of mirror face with original face yields identity. -/
theorem mirror_face_apply (G : Hypermap) (x : G.Dart) :
    G.face ((mirror G).face x) = x :=
  Function.rightInverse_invFun G.face_surjective x

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

/-! ## One-step glink witnesses and gcomp lifts -/

/-- The edge-step is a glink. -/
theorem glinkE (G : Hypermap) (x : G.Dart) : glink G x (G.edge x) := Or.inl rfl

/-- The node-step is a glink. -/
theorem glinkN' (G : Hypermap) (x : G.Dart) : glink G x (G.node x) := Or.inr (Or.inl rfl)

/-- The face-step is a glink. -/
theorem glinkF' (G : Hypermap) (x : G.Dart) : glink G x (G.face x) := Or.inr (Or.inr rfl)

theorem gcomp_edge (G : Hypermap) (x : G.Dart) : gcomp G x (G.edge x) :=
  Relation.ReflTransGen.single (glinkE G x)

theorem gcomp_node (G : Hypermap) (x : G.Dart) : gcomp G x (G.node x) :=
  Relation.ReflTransGen.single (glinkN' G x)

theorem gcomp_face (G : Hypermap) (x : G.Dart) : gcomp G x (G.face x) :=
  Relation.ReflTransGen.single (glinkF' G x)

theorem gcomp_of_cedge (G : Hypermap) {x y : G.Dart} (h : cedge G x y) : gcomp G x y := by
  obtain ⟨n, rfl⟩ := h
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact Relation.ReflTransGen.tail ih (glinkE G _)

theorem gcomp_of_cnode (G : Hypermap) {x y : G.Dart} (h : cnode G x y) : gcomp G x y := by
  obtain ⟨n, rfl⟩ := h
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact Relation.ReflTransGen.tail ih (glinkN' G _)

theorem gcomp_of_cface (G : Hypermap) {x y : G.Dart} (h : cface G x y) : gcomp G x y := by
  obtain ⟨n, rfl⟩ := h
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact Relation.ReflTransGen.tail ih (glinkF' G _)

/-- In a connected hypermap every pair of darts is gcomp-related. -/
theorem Connected.gcomp {G : Hypermap} (h : Connected G) (x y : G.Dart) :
    gcomp G x y := h x y

/-! ## clink path-lifting lemmas (for jordan_walkupE) -/

-- Coq: hypermap.v (connect_refl)
theorem cconnect_refl (G : Hypermap) (x : G.Dart) : cconnect G x x :=
  Relation.ReflTransGen.refl

-- Coq: hypermap.v (connect_trans)
theorem cconnect_trans (G : Hypermap) : Transitive (cconnect G) :=
  fun _ _ _ => Relation.ReflTransGen.trans

-- Coq: hypermap.v (clinkN)
theorem clinkN (G : Hypermap) (x : G.Dart) : clink G (G.node x) x :=
  Or.inl rfl

-- Coq: hypermap.v (clinkF)
theorem clinkF (G : Hypermap) (x : G.Dart) : clink G x (G.face x) :=
  Or.inr rfl

-- Coq: hypermap.v (connect_node)
theorem cconnect_node (G : Hypermap) (x : G.Dart) : cconnect G (G.node x) x :=
  Relation.ReflTransGen.single (clinkN G x)

-- Coq: hypermap.v (connect_face)
theorem cconnect_face (G : Hypermap) (x : G.Dart) : cconnect G x (G.face x) :=
  Relation.ReflTransGen.single (clinkF G x)

-- Coq: hypermap.v (path lifting / cons)
theorem cconnect_cons (G : Hypermap) {x y z : G.Dart}
    (h : clink G x y) (hr : cconnect G y z) : cconnect G x z :=
  Relation.ReflTransGen.head h hr

/-- A single clink step is a cconnect path. -/
theorem cconnect_of_clink {G : Hypermap} {x y : G.Dart}
    (h : clink G x y) : cconnect G x y :=
  Relation.ReflTransGen.single h

/-- Append a clink step on the right of a cconnect path. -/
theorem cconnect_snoc {G : Hypermap} {x y z : G.Dart}
    (hr : cconnect G x y) (h : clink G y z) : cconnect G x z :=
  Relation.ReflTransGen.tail hr h

-- TODO: cconnect_symm — reversing a single clink step requires iterating
-- around finite permutation orbits (face-forward or node-backward), which
-- needs the order-of-permutation machinery. Left for a future PR.

/-! ## Key planarity theorems -/

-- The even genus property (even_genusP) and Euler inequality (euler_le)
-- are proved in Jordan.lean via Walkup induction.
-- They are available as Hypermap.even_genusP and Hypermap.euler_le
-- after importing FourColor.Jordan.

/-! ## Connected / Planar / nComp shape helpers -/

theorem connected_intro {G : Hypermap} (h : ∀ x y : G.Dart, gcomp G x y) :
    Connected G := h

theorem connected_all_gcomp {G : Hypermap} (h : Connected G) (x y : G.Dart) :
    gcomp G x y := h x y

/-- Every hypermap has at least one connected component. -/
theorem nComp_refl (G : Hypermap) : 1 ≤ nComp G := by
  by_contra h_contra
  convert Fintype.card_pos_iff.mpr _
  · exact Iff.symm (iff_false_intro h_contra)
  · exact ⟨Quotient.mk'' (Classical.arbitrary _)⟩

theorem Planar.genus_eq_zero {G : Hypermap} (h : Planar G) : genus G = 0 := h
theorem Planar.intro {G : Hypermap} (h : genus G = 0) : Planar G := h
theorem Planar.iff_genus_zero (G : Hypermap) : Planar G ↔ genus G = 0 := Iff.rfl

theorem Planar.eulerLhs_eq {G : Hypermap} (_h : Planar G) :
    eulerLhs G = 2 * 0 + eulerRhs G → eulerLhs G = eulerRhs G := by
  intro heq; simp at heq; exact heq

/-! ## Dual bijectivity helpers -/

theorem mirror_Dart_eq (G : Hypermap) : (mirror G).Dart = G.Dart := rfl
theorem dual_Dart_eq (G : Hypermap) : (dual G).Dart = G.Dart := rfl

theorem dual_edge_bijective (G : Hypermap) :
    Function.Bijective (dual G).edge := by
  show Function.Bijective (Function.invFun G.edge)
  exact ⟨(Function.rightInverse_invFun G.edge_surjective).injective,
         fun y => ⟨G.edge y, Function.leftInverse_invFun G.edge_injective y⟩⟩

theorem dual_node_bijective (G : Hypermap) :
    Function.Bijective (dual G).node := by
  show Function.Bijective (Function.invFun G.face)
  exact ⟨(Function.rightInverse_invFun G.face_surjective).injective,
         fun y => ⟨G.face y, Function.leftInverse_invFun G.face_injective y⟩⟩

theorem dual_face_bijective (G : Hypermap) :
    Function.Bijective (dual G).face := by
  show Function.Bijective (Function.invFun G.node)
  exact ⟨(Function.rightInverse_invFun G.node_surjective).injective,
         fun y => ⟨G.node y, Function.leftInverse_invFun G.node_injective y⟩⟩

/-! ## More mem2 helpers -/

theorem List.mem2.indices_lt {α : Type*} {p : List α} {a b : α}
    (h : List.mem2 p a b) :
    ∃ i j, i < j ∧ j < p.length ∧ p[i]? = some a ∧ p[j]? = some b := h

theorem List.mem2.length_ge_two {α : Type*} {p : List α} {a b : α}
    (h : List.mem2 p a b) : 2 ≤ p.length := by
  obtain ⟨_, _, _, _, _, _⟩ := h
  omega

theorem List.not_mem2_singleton {α : Type*} (x a b : α) :
    ¬ List.mem2 [x] a b := by
  intro h
  have := h.length_ge_two
  simp at this

/-! ## MoebiusPath cons-shape helpers -/

/-- A Moebius path is duplicate-free. -/
theorem MoebiusPath.nodup {G : Hypermap} {q : List G.Dart}
    (h : MoebiusPath G q) : q.Nodup := by
  match q, h with
  | x :: p, ⟨hnodup, _, _⟩ => exact hnodup

/-- A Moebius path's clink-chain. -/
theorem MoebiusPath.chain {G : Hypermap} {x : G.Dart} {p : List G.Dart}
    (h : MoebiusPath G (x :: p)) : List.IsChain (clink G) (x :: p) := h.2.1

/-- A Moebius path's mem2 twist. -/
theorem MoebiusPath.twist {G : Hypermap} {x : G.Dart} {p : List G.Dart}
    (h : MoebiusPath G (x :: p)) :
    List.mem2 p (G.finvNode ((x :: p).getLast (List.cons_ne_nil x p))) (G.node x) :=
  h.2.2

theorem MoebiusPath.head_not_in_tail {G : Hypermap} {x : G.Dart} {p : List G.Dart}
    (h : MoebiusPath G (x :: p)) : x ∉ p := by
  obtain ⟨hnodup, _, _⟩ := h
  exact (List.nodup_cons.mp hnodup).1

theorem MoebiusPath.cons_ne_nil {G : Hypermap} {x : G.Dart} {p : List G.Dart}
    (h : MoebiusPath G (x :: p)) : p ≠ [] := by
  intro hp
  have hge := MoebiusPath.length_ge_two h
  rw [hp, List.length_cons, List.length_nil] at hge
  omega

/-- A MoebiusPath has length ≥ 2 (alias-style cons form). -/
theorem MoebiusPath.cons_length_ge_two {G : Hypermap} {x : G.Dart} {p : List G.Dart}
    (h : MoebiusPath G (x :: p)) : 2 ≤ (x :: p).length :=
  MoebiusPath.length_ge_two h

/-- The tail of a MoebiusPath is nonempty. -/
theorem MoebiusPath.tail_ne_nil {G : Hypermap} {x : G.Dart} {p : List G.Dart}
    (h : MoebiusPath G (x :: p)) : p ≠ [] := MoebiusPath.cons_ne_nil h

/-- The head of a MoebiusPath is in the path. -/
theorem MoebiusPath.head_mem {G : Hypermap} {x : G.Dart} {p : List G.Dart}
    (_h : MoebiusPath G (x :: p)) : x ∈ (x :: p) := List.mem_cons_self ..

/-- Two distinct elements of a MoebiusPath. -/
theorem MoebiusPath.head_ne_tail_head {G : Hypermap} {x : G.Dart} {p : List G.Dart}
    (h : MoebiusPath G (x :: p)) (y : G.Dart) (hy : y ∈ p) : x ≠ y := by
  intro hxy
  exact MoebiusPath.head_not_in_tail h (hxy ▸ hy)

/-- The path of a MoebiusPath has at least 2 elements (length ≥ 2 form). -/
theorem MoebiusPath.length_pos {G : Hypermap} {q : List G.Dart}
    (h : MoebiusPath G q) : 0 < q.length := by
  have h2 := MoebiusPath.length_ge_two h
  omega

/-- A MoebiusPath, viewed as a List, has positive length. -/
theorem MoebiusPath.exists_head {G : Hypermap} {q : List G.Dart}
    (h : MoebiusPath G q) : ∃ x p, q = x :: p := by
  match q, h with
  | x :: p, _ => exact ⟨x, p, rfl⟩

/-! ## edgePerm / nodePerm / facePerm apply simp lemmas -/

@[simp] theorem edgePerm_apply {G : Hypermap} (x : G.Dart) :
    G.edgePerm x = G.edge x := rfl

@[simp] theorem nodePerm_apply {G : Hypermap} (x : G.Dart) :
    G.nodePerm x = G.node x := rfl

@[simp] theorem facePerm_apply {G : Hypermap} (x : G.Dart) :
    G.facePerm x = G.face x := rfl

theorem edgePerm_symm_apply {G : Hypermap} (x : G.Dart) :
    G.edgePerm.symm x = G.finvEdge x := rfl

theorem nodePerm_symm_apply {G : Hypermap} (x : G.Dart) :
    G.nodePerm.symm x = G.finvNode x := rfl

theorem facePerm_symm_apply {G : Hypermap} (x : G.Dart) :
    G.facePerm.symm x = G.finvFace x := rfl

/-! ## invFun double-negation for bijections -/

theorem invFun_invFun_eq {α : Type*} [Nonempty α] {f : α → α}
    (hf_inj : Function.Injective f) (hf_surj : Function.Surjective f) (x : α) :
    Function.invFun (Function.invFun f) x = f x := by
  obtain ⟨y, rfl⟩ := hf_surj x
  have h_inv_inv : Function.invFun (Function.invFun f) (Function.invFun f (f (f y)))
      = f (f y) := by
    apply Function.leftInverse_invFun
    exact Function.LeftInverse.injective (Function.rightInverse_invFun hf_surj)
  rwa [Function.leftInverse_invFun hf_inj] at h_inv_inv

/-! ## dual_dual involutivity -/

theorem dual_dual_edge (G : Hypermap) (x : G.Dart) :
    (dual (dual G)).edge x = G.edge x := by
  simp only [dual_edge]
  exact invFun_invFun_eq edge_injective edge_surjective x

theorem dual_dual_node (G : Hypermap) (x : G.Dart) :
    (dual (dual G)).node x = G.node x := by
  simp only [dual_node, dual_face]
  exact invFun_invFun_eq node_injective node_surjective x

theorem dual_dual_face (G : Hypermap) (x : G.Dart) :
    (dual (dual G)).face x = G.face x := by
  simp only [dual_face, dual_node]
  exact invFun_invFun_eq face_injective face_surjective x

/-! ## mirror_mirror involutivity -/

theorem mirror_mirror_edge (G : Hypermap) (x : G.Dart) :
    (mirror (mirror G)).edge x = G.edge x := by
  show Function.invFun G.face (Function.invFun G.node x) = G.edge x
  rw [← Function.leftInverse_invFun G.face_injective (G.edge x),
      ← Function.leftInverse_invFun G.node_injective (G.face (G.edge x))]
  rw [G.edgeK']

theorem mirror_mirror_node (G : Hypermap) (x : G.Dart) :
    (mirror (mirror G)).node x = G.node x := by
  simp only [mirror_node]
  exact invFun_invFun_eq node_injective node_surjective x

theorem mirror_mirror_face (G : Hypermap) (x : G.Dart) :
    (mirror (mirror G)).face x = G.face x := by
  simp only [mirror_face]
  exact invFun_invFun_eq face_injective face_surjective x

@[simp] theorem mirror_mirror_node_eq (G : Hypermap) : (mirror (mirror G)).node = G.node :=
  funext (mirror_mirror_node G)

@[simp] theorem mirror_mirror_face_eq (G : Hypermap) : (mirror (mirror G)).face = G.face :=
  funext (mirror_mirror_face G)

@[simp] theorem dual_mirror_dart_eq (G : Hypermap) : (dual (mirror G)).Dart = G.Dart := rfl

@[simp] theorem mirror_dual_dart_eq (G : Hypermap) : (mirror (dual G)).Dart = G.Dart := rfl

/-! ## eulerLhs / eulerRhs / genus / numOrbits unfolders -/

theorem numOrbits_def {G : Hypermap} (σ : Equiv.Perm G.Dart) :
    numOrbits σ = σ.cycleFactorsFinset.card + (Fintype.card G.Dart - σ.support.card) :=
  rfl

theorem fcardEdge_def (G : Hypermap) :
    fcardEdge G = numOrbits G.edgePerm := rfl

theorem fcardNode_def (G : Hypermap) :
    fcardNode G = numOrbits G.nodePerm := rfl

theorem fcardFace_def (G : Hypermap) :
    fcardFace G = numOrbits G.facePerm := rfl

theorem eulerLhs_def (G : Hypermap) :
    eulerLhs G = 2 * nComp G + Fintype.card G.Dart := rfl

theorem eulerRhs_def (G : Hypermap) :
    eulerRhs G = fcardEdge G + fcardNode G + fcardFace G := rfl

theorem genus_def (G : Hypermap) :
    genus G = (eulerLhs G - eulerRhs G) / 2 := rfl

/-! ## Connected component count via gcomp -/

theorem gcomp_imp_eqvGen (G : Hypermap) {x y : G.Dart} (h : gcomp G x y) :
    Relation.EqvGen (glink G) x y := by
  induction h
  · exact Relation.EqvGen.refl _
  · exact Relation.EqvGen.trans _ _ _ ‹_› (Relation.EqvGen.rel _ _ ‹_›)

theorem connected_glinkSetoid_trivial {G : Hypermap} (hc : Connected G)
    (a b : G.Dart) : (glinkSetoid G).r a b := by
  apply gcomp_imp_eqvGen; exact hc a b

/-- A connected hypermap has exactly one connected component. -/
theorem nComp_eq_one_of_connected (G : Hypermap) (hc : Connected G) :
    nComp G = 1 := by
  convert Fintype.card_eq_one_iff.mpr _
  exact ⟨Quotient.mk'' (Classical.arbitrary G.Dart),
    fun y => by obtain ⟨x⟩ := y
                exact Quotient.sound (connected_glinkSetoid_trivial hc _ _)⟩

/-- Every connected hypermap has a positive number of connected components. -/
theorem nComp_pos_of_connected (G : Hypermap) (_h : Connected G) : 0 < nComp G :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one (nComp_refl G)

/-! ## gcomp_glink: lifting and chaining helpers -/

/-- A direct gcomp lift from glink. -/
theorem gcomp_of_glink (G : Hypermap) {x y : G.Dart} (h : glink G x y) :
    gcomp G x y := Relation.ReflTransGen.single h

/-- Two glink steps compose to gcomp. -/
theorem gcomp_two (G : Hypermap) {x y z : G.Dart}
    (hxy : glink G x y) (hyz : glink G y z) : gcomp G x z :=
  Relation.ReflTransGen.head hxy (Relation.ReflTransGen.single hyz)

/-- gcomp is an equivalence relation. -/
theorem gcomp_equivalence (G : Hypermap) : Equivalence (gcomp G) :=
  ⟨gcomp_refl G, fun h => gcomp_symm h, fun hab hbc => gcomp_trans G hab hbc⟩

/-! ## Dual–mirror cross-construction lemmas -/

@[simp] theorem dual_mirror_edge (G : Hypermap) (x : G.Dart) :
    (dual (mirror G)).edge x = Function.invFun ((mirror G).edge) x := rfl

@[simp] theorem mirror_dual_edge (G : Hypermap) (x : G.Dart) :
    (mirror (dual G)).edge x = (dual G).face ((dual G).node x) := rfl

theorem dual_swaps_node_face (G : Hypermap) :
    (dual G).node = Function.invFun G.face ∧ (dual G).face = Function.invFun G.node :=
  ⟨rfl, rfl⟩

/-! ## Dart-cardinality helpers -/

/-- The number of darts in a hypermap is positive when `Dart` is nonempty. -/
theorem card_Dart_pos (G : Hypermap) [Nonempty G.Dart] : 0 < Fintype.card G.Dart :=
  Fintype.card_pos

/-- The dual hypermap has the same number of darts. -/
theorem card_dual_dart (G : Hypermap) : Fintype.card (dual G).Dart = Fintype.card G.Dart :=
  rfl

/-- The mirror hypermap has the same number of darts. -/
theorem card_mirror_dart (G : Hypermap) : Fintype.card (mirror G).Dart = Fintype.card G.Dart :=
  rfl

theorem card_dual_dart_eq (G : Hypermap) : Fintype.card (dual G).Dart = Fintype.card G.Dart := rfl

theorem card_mirror_dual_dart (G : Hypermap) :
    Fintype.card (mirror (dual G)).Dart = Fintype.card G.Dart := rfl

theorem card_dual_mirror_dart (G : Hypermap) :
    Fintype.card (dual (mirror G)).Dart = Fintype.card G.Dart := rfl

theorem card_dual_dual_dart (G : Hypermap) :
    Fintype.card (dual (dual G)).Dart = Fintype.card G.Dart := rfl

theorem card_mirror_mirror_dart (G : Hypermap) :
    Fintype.card (mirror (mirror G)).Dart = Fintype.card G.Dart := rfl

/-! ## Permutation invFun cancellation and iterate base cases -/

theorem face_invFun_face (G : Hypermap) (x : G.Dart) :
    Function.invFun G.face (G.face x) = x :=
  Function.leftInverse_invFun G.face_injective x

theorem edge_invFun_edge (G : Hypermap) (x : G.Dart) :
    Function.invFun G.edge (G.edge x) = x :=
  Function.leftInverse_invFun G.edge_injective x

theorem node_invFun_node (G : Hypermap) (x : G.Dart) :
    Function.invFun G.node (G.node x) = x :=
  Function.leftInverse_invFun G.node_injective x

@[simp] theorem face_iter_zero (G : Hypermap) (x : G.Dart) : G.face^[0] x = x := rfl

@[simp] theorem edge_iter_zero (G : Hypermap) (x : G.Dart) : G.edge^[0] x = x := rfl

@[simp] theorem node_iter_zero (G : Hypermap) (x : G.Dart) : G.node^[0] x = x := rfl

theorem face_iter_one (G : Hypermap) (x : G.Dart) : G.face^[1] x = G.face x := rfl

theorem edge_iter_one (G : Hypermap) (x : G.Dart) : G.edge^[1] x = G.edge x := rfl

theorem node_iter_one (G : Hypermap) (x : G.Dart) : G.node^[1] x = G.node x := rfl

theorem face_iter_succ (G : Hypermap) (x : G.Dart) (n : ℕ) :
    G.face^[n + 1] x = G.face (G.face^[n] x) := by
  rw [Function.iterate_succ_apply']

theorem edge_iter_succ (G : Hypermap) (x : G.Dart) (n : ℕ) :
    G.edge^[n + 1] x = G.edge (G.edge^[n] x) := by
  rw [Function.iterate_succ_apply']

theorem node_iter_succ (G : Hypermap) (x : G.Dart) (n : ℕ) :
    G.node^[n + 1] x = G.node (G.node^[n] x) := by
  rw [Function.iterate_succ_apply']

theorem face_iter_add (G : Hypermap) (x : G.Dart) (m n : ℕ) :
    G.face^[m + n] x = G.face^[m] (G.face^[n] x) := by
  rw [Function.iterate_add_apply]

theorem edge_iter_add (G : Hypermap) (x : G.Dart) (m n : ℕ) :
    G.edge^[m + n] x = G.edge^[m] (G.edge^[n] x) := by
  rw [Function.iterate_add_apply]

theorem node_iter_add (G : Hypermap) (x : G.Dart) (m n : ℕ) :
    G.node^[m + n] x = G.node^[m] (G.node^[n] x) := by
  rw [Function.iterate_add_apply]

@[simp] theorem dual_dual_edge_eq (G : Hypermap) : (dual (dual G)).edge = G.edge := by
  funext x; exact dual_dual_edge G x

@[simp] theorem dual_dual_node_eq (G : Hypermap) : (dual (dual G)).node = G.node := by
  funext x; exact dual_dual_node G x

@[simp] theorem dual_dual_face_eq (G : Hypermap) : (dual (dual G)).face = G.face := by
  funext x; exact dual_dual_face G x

/-- `glink (dual G) x y` is equivalent to `glink G y x`: the dual reverses
    the direction of every graph link. -/
theorem glink_dual_iff (G : Hypermap) (x y : G.Dart) :
    glink (dual G) x y ↔ Function.swap (glink G) x y :=
  ⟨fun h => h.elim
    (fun he => Or.inl (he ▸ Function.rightInverse_invFun edge_surjective x))
    (fun h => h.elim
      (fun hn => Or.inr (Or.inr (hn ▸ Function.rightInverse_invFun face_surjective x)))
      (fun hf => Or.inr (Or.inl (hf ▸ Function.rightInverse_invFun node_surjective x)))),
   fun h => h.elim
    (fun he => Or.inl (he ▸ Function.leftInverse_invFun edge_injective y))
    (fun h => h.elim
      (fun hn => Or.inr (Or.inr (hn ▸ Function.leftInverse_invFun node_injective y)))
      (fun hf => Or.inr (Or.inl (hf ▸ Function.leftInverse_invFun face_injective y))))⟩

/-- `gcomp` commutes with `dual` by swapping arguments. -/
theorem gcomp_dual (G : Hypermap) (x y : G.Dart) :
    gcomp (dual G) x y ↔ gcomp G y x :=
  ⟨fun h =>
    Relation.ReflTransGen.mono (fun _ _ h => h)
      (Relation.ReflTransGen.swap
        (Relation.ReflTransGen.mono (fun a b hab => (glink_dual_iff G a b).mp hab) h)),
   fun h =>
    Relation.ReflTransGen.mono (fun a b hab => (glink_dual_iff G a b).mpr hab)
      (Relation.ReflTransGen.swap h)⟩

/-- Connectivity is preserved by dual. -/
theorem Connected.dual {G : Hypermap} (h : Connected G) : Connected (dual G) :=
  fun x y =>
    Relation.ReflTransGen.mono
      (fun a b hab => (glink_dual_iff G a b).mpr hab)
      (Relation.ReflTransGen.swap (h y x))

/-- Connectivity is invariant under dual (iff form). -/
theorem Connected_iff_dual (G : Hypermap) : Connected G ↔ Connected (dual G) := by
  refine ⟨Connected.dual, fun h => ?_⟩
  intro x y
  exact gcomp_symm ((gcomp_dual G x y).mp (h x y))

/-- Connectivity is preserved by `dual ∘ dual` (which equals identity on most fields). -/
theorem Connected.dual_dual {G : Hypermap} (h : Connected G) : Connected (Hypermap.dual (Hypermap.dual G)) :=
  Connected.dual (Connected.dual h)

/-- glink is invariant under double dual (since dual is involutive). -/
theorem glink_dual_dual_eq (G : Hypermap) :
    glink (dual (dual G)) = glink G := by
  funext x y
  unfold glink
  rw [dual_dual_edge_eq, dual_dual_node_eq, dual_dual_face_eq]

/-- gcomp is invariant under double dual. -/
@[simp] theorem gcomp_dual_dual_iff (G : Hypermap) (x y : G.Dart) :
    gcomp (dual (dual G)) x y ↔ gcomp G x y := by
  unfold gcomp
  rw [glink_dual_dual_eq]

end Hypermap