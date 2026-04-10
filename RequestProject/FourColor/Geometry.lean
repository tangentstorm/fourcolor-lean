/-
Copyright (c) 2006-2018 Microsoft Corporation and Inria (Coq version).
Lean 4 port of the Four Color Theorem formalization.

The geometrical interpretation of hypermap: bridgeless, plain, cubic,
and related properties used throughout the Four Color Theorem proof.
-/
import RequestProject.FourColor.Hypermap

set_option maxHeartbeats 400000

open Hypermap

namespace Hypermap

variable (G : Hypermap)

/-! ## Bridgeless and loopless -/

/-- A hypermap is bridgeless if no face cycle contains both endpoints of
    an edge link: ¬∃ x, cface x (edge x). -/
def Bridgeless : Prop :=
  ∀ x : G.Dart, ¬ cface G x (G.edge x)

/-- A hypermap is loopless if no node cycle contains both endpoints of
    an edge link. -/
def Loopless : Prop :=
  ∀ x : G.Dart, ¬ cnode G x (G.edge x)

/-! ## Plain (simple) and cubic -/

/-- The order of dart x under permutation f: the minimal period of iteration.
    Uses Mathlib's `Function.minimalPeriod`. -/
noncomputable def orderOf (f : G.Dart → G.Dart) (x : G.Dart) : ℕ :=
  Function.minimalPeriod f x

/-- A hypermap is plain if every edge orbit has exactly 2 elements. -/
def Plain : Prop :=
  ∀ x : G.Dart, G.edge (G.edge x) = x ∧ G.edge x ≠ x

/-- A hypermap is cubic if every node orbit has exactly 3 elements. -/
def Cubic : Prop :=
  ∀ x : G.Dart, G.node (G.node (G.node x)) = x ∧
    G.node x ≠ x ∧ G.node (G.node x) ≠ x

/-- A hypermap is precubic if every node orbit has at most 3 elements. -/
def Precubic : Prop :=
  ∀ x : G.Dart, G.node (G.node (G.node x)) = x

/-- A hypermap is quasicubic relative to a set r if all nodes NOT in r
    have exactly 3 elements. -/
def Quasicubic (r : Finset G.Dart) : Prop :=
  ∀ x : G.Dart, x ∉ r → G.node (G.node (G.node x)) = x ∧
    G.node x ≠ x ∧ G.node (G.node x) ≠ x

/-- The arity (face order) of a dart. -/
noncomputable def arity (x : G.Dart) : ℕ :=
  orderOf G G.face x

/-- A hypermap is pentagonal if all faces have size at least 5. -/
def Pentagonal : Prop :=
  ∀ x : G.Dart, 5 ≤ arity G x

/-! ## Face adjacency -/

/-- Two darts are adjacent if their faces share a node link:
    ∃ z, cface x z ∧ cface y (node z). -/
def adj (x y : G.Dart) : Prop :=
  ∃ z : G.Dart, cface G x z ∧ cface G y (G.node z)

/-! ## Simple paths and rings -/

/-- A sequence of darts is face-simple: no two darts lie in the same face. -/
def Simple (p : List G.Dart) : Prop :=
  p.Pairwise (fun x y => ¬ cface G x y)

/-- The rlink relation: cface (node x) y. -/
def rlink (x y : G.Dart) : Prop :=
  cface G (G.node x) y

/-- A simple R-cycle (ring): a face-simple cyclic rlink path. -/
def Srcycle (r : List G.Dart) : Prop :=
  r.Nodup ∧ Simple G r ∧ r.length > 0 ∧
  (∀ i : Fin r.length,
    rlink G (r.get i)
      (r.get ⟨(i.val + 1) % r.length, by
        have := i.isLt; exact Nat.mod_lt _ (by omega)⟩))

/-! ## Face band and kernel -/

/-- The face band of a sequence: the set of darts face-connected to
    some element of the sequence. -/
def fband (p : List G.Dart) (x : G.Dart) : Prop :=
  ∃ y ∈ p, cface G x y

/-- The kernel: darts NOT in the face band. -/
def kernel (p : List G.Dart) (x : G.Dart) : Prop :=
  ¬ fband G p x

/-! ## Edge insertion (for plain maps) -/

/-- The edge closure of a sequence (for plain maps): interleave each
    dart with its edge. -/
def insertE (p : List G.Dart) : List G.Dart :=
  p.flatMap (fun x => [x, G.edge x])

/-! ## Bundled geometry structures -/

/-- A hypermap that is both planar and bridgeless. -/
structure PlanarBridgeless extends Hypermap where
  planar : Planar toHypermap
  bridgeless : Bridgeless toHypermap

/-- A hypermap that is planar, bridgeless, plain, and precubic. -/
structure PlanarBridgelessPlainPrecubic extends Hypermap where
  planar : Planar toHypermap
  bridgeless : Bridgeless toHypermap
  plain : Plain toHypermap
  precubic : Precubic toHypermap

end Hypermap
