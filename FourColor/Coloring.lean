/-
Copyright (c) 2006-2018 Microsoft Corporation and Inria (Coq version).
Lean 4 port of the Four Color Theorem formalization.

Hypermap and graph colorings, colorable maps, ring traces, valid contracts,
and the definition of the special maps used in the proof: minimal counter
example, C-reducible, and embeddable.
-/
import FourColor.Hypermap
import FourColor.Color
import FourColor.Geometry
import FourColor.Chromogram

set_option maxHeartbeats 400000

open Hypermap Color Classical

noncomputable section

namespace Hypermap

variable {G : Hypermap}

/-! ## Map coloring -/

/-- A proper map coloring of a hypermap: a function k : Dart → Color such that
    - k is constant on each face orbit (invariant under face)
    - k differs across each edge link (not invariant under edge)
    This corresponds to a proper coloring of the dual graph. -/
def Coloring (k : G.Dart → Color) : Prop :=
  (∀ x, k (G.edge x) ≠ k x) ∧
  (∀ x, k (G.face x) = k x)

/-- A hypermap is four-colorable if it admits a proper coloring. -/
def FourColorable (G : Hypermap) : Prop :=
  ∃ k : G.Dart → Color, Coloring k

/-- Four-colorability implies bridgelessness. -/
theorem four_colorable_bridgeless : FourColorable G → Bridgeless G := by
  intro ⟨k, hkE, hkF⟩ x hcf
  apply hkE x
  -- If cface x (edge x), then k x = k (edge x) by face-invariance,
  -- contradicting edge-distinctness.
  obtain ⟨n, hn⟩ := hcf
  have : k (G.edge x) = k x := by
    rw [← hn]
    clear hn
    induction n with
    | zero => simp [Function.iterate_zero]
    | succ n ih =>
      rw [Function.iterate_succ', Function.comp_apply, hkF]
      exact ih
  exact this

/-! ## Coloring composition with injection -/

-- Coq: coloring.v:81
/-- Composing a coloring with an injective function yields a coloring. -/
theorem coloring_inj {h : Color → Color} (hinj : Function.Injective h)
    {k : G.Dart → Color} (hk : Coloring k) : Coloring (h ∘ k) := by
  obtain ⟨hkE, hkF⟩ := hk
  exact ⟨fun x => hinj.ne (hkE x), fun x => congr_arg h (hkF x)⟩

/-! ## Mirror coloring -/

-- Coq: coloring.v:139
/-- A coloring of the mirror hypermap induces a coloring of the original. -/
theorem coloring_mirror {k : (mirror G).Dart → Color}
    (hk : @Coloring (mirror G) k) : @Coloring G k := by
  obtain ⟨hkE, hkF⟩ := hk
  -- Face invariance: mirror.face = invFun G.face, so k ∘ face⁻¹ = k implies k ∘ face = k.
  have hface : ∀ x, k (G.face x) = k x := by
    intro x
    have h := hkF (G.face x)
    change k (Function.invFun G.face (G.face x)) = k (G.face x) at h
    rw [Function.leftInverse_invFun face_bijective.injective] at h
    exact h.symm
  -- Node distinctness: mirror.edge = face ∘ node, so k(face(node x)) ≠ k x.
  -- By face invariance, k(node x) ≠ k x.
  have hnode_ne : ∀ x, k (G.node x) ≠ k x := by
    intro x
    have h := hkE x
    change k (G.face (G.node x)) ≠ k x at h
    rwa [hface (G.node x)] at h
  -- Edge distinctness: from edgeK, n(f(e(x))) = x, so specializing
  -- hnode_ne at f(e(x)) gives k(x) ≠ k(f(e(x))) = k(e(x)).
  constructor
  · intro x heq
    exact hnode_ne (G.face (G.edge x)) (by rw [edgeK', hface]; exact heq.symm)
  · exact hface

-- Coq: coloring.v:147
/-- If the mirror of G is four-colorable, then G is four-colorable. -/
theorem colorable_mirror (h : FourColorable (mirror G)) : FourColorable G := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, coloring_mirror hk⟩

/-! ## Graph coloring (dual) -/

/-- A graph coloring: constant on nodes, distinct on edges. -/
def GraphColoring (k : G.Dart → Color) : Prop :=
  (∀ x, k (G.edge x) ≠ k x) ∧
  (∀ x, k (G.node x) = k x)

/-- A hypermap is graph-four-colorable. -/
def GraphFourColorable (G : Hypermap) : Prop :=
  ∃ k : G.Dart → Color, GraphColoring k

/-! ## Dual coloring -/

-- Coq: coloring.v:123
/-- A coloring on the dual hypermap corresponds to a graph coloring. -/
theorem coloring_dual {k : G.Dart → Color} :
    @Coloring (dual G) k ↔ GraphColoring k := by
  constructor
  · intro ⟨hkE, hkF⟩
    constructor
    · intro x
      have h := hkE (G.edge x)
      change k (Function.invFun G.edge (G.edge x)) ≠ k (G.edge x) at h
      rw [Function.leftInverse_invFun edge_bijective.injective] at h
      exact Ne.symm h
    · intro x
      have h := hkF (G.node x)
      change k (Function.invFun G.node (G.node x)) = k (G.node x) at h
      rw [Function.leftInverse_invFun node_bijective.injective] at h
      exact h.symm
  · intro ⟨hkE, hkN⟩
    constructor
    · intro x
      obtain ⟨y, hy⟩ := @edge_surjective G x
      subst hy
      show k (Function.invFun G.edge (G.edge y)) ≠ k (G.edge y)
      rw [Function.leftInverse_invFun edge_bijective.injective]
      exact Ne.symm (hkE y)
    · intro x
      obtain ⟨y, hy⟩ := @node_surjective G x
      subst hy
      show k (Function.invFun G.node (G.node y)) = k (G.node y)
      rw [Function.leftInverse_invFun node_bijective.injective]
      exact (hkN y).symm

-- Coq: coloring.v:135
/-- Four-colorability of the dual corresponds to graph-four-colorability. -/
theorem four_colorable_dual : FourColorable (dual G) ↔ GraphFourColorable G := by
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, coloring_dual.mp hk⟩
  · rintro ⟨k, hk⟩; exact ⟨k, coloring_dual.mpr hk⟩

/-! ## Coloring projections -/

-- Coq: coloring.v – projection helpers for GraphColoring
/-- Edge-distinctness from a graph coloring. -/
theorem GraphColoring.edge_distinct {G : Hypermap} {k : G.Dart → Color}
    (h : GraphColoring k) : ∀ x, k (G.edge x) ≠ k x := h.1

/-- Node-invariance from a graph coloring. -/
theorem GraphColoring.node_invariant {G : Hypermap} {k : G.Dart → Color}
    (h : GraphColoring k) : ∀ x, k (G.node x) = k x := h.2

-- Coq: coloring.v – projection helpers for Coloring
/-- Edge-distinctness from a (map) coloring. -/
theorem Coloring.edge_distinct {G : Hypermap} {k : G.Dart → Color}
    (h : Coloring k) : ∀ x, k (G.edge x) ≠ k x := h.1

/-- Face-invariance from a (map) coloring. -/
theorem Coloring.face_invariant {G : Hypermap} {k : G.Dart → Color}
    (h : Coloring k) : ∀ x, k (G.face x) = k x := h.2

-- Coq: coloring.v – cface-invariance of a coloring
/-- A Coloring is constant on cface-orbits. -/
theorem Coloring.cface {G : Hypermap} {k : G.Dart → Color}
    (h : Coloring k) {x y : G.Dart} (hc : cface G x y) : k y = k x := by
  obtain ⟨n, rfl⟩ := hc
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', h.face_invariant]
    exact ih

/-! ## Contract coloring -/

/-- A contract coloring for a set of contracted edges cc:
    k is invariant under face, and invariant under edge exactly
    on the edges in the contract cc. -/
def CcColoring (cc : Finset G.Dart) (k : G.Dart → Color) : Prop :=
  (∀ x, x ∉ cc ∧ G.edge x ∉ cc → k (G.edge x) ≠ k x) ∧
  (∀ x, x ∈ cc ∨ G.edge x ∈ cc → k (G.edge x) = k x) ∧
  (∀ x, k (G.face x) = k x)

/-- Contractibility: existence of a contract coloring. -/
def CcColorable (cc : Finset G.Dart) : Prop :=
  ∃ k : G.Dart → Color, CcColoring cc k

/-! ## CcColoring projections -/

-- Coq: coloring.v – projection helpers for CcColoring
/-- Off-contract edge-distinctness from a contract coloring. -/
theorem CcColoring.edge_off_cc {G : Hypermap} {cc : Finset G.Dart} {k : G.Dart → Color}
    (h : CcColoring cc k) : ∀ x, x ∉ cc ∧ G.edge x ∉ cc → k (G.edge x) ≠ k x := h.1

/-- On-contract edge-invariance from a contract coloring. -/
theorem CcColoring.edge_on_cc {G : Hypermap} {cc : Finset G.Dart} {k : G.Dart → Color}
    (h : CcColoring cc k) : ∀ x, x ∈ cc ∨ G.edge x ∈ cc → k (G.edge x) = k x := h.2.1

/-- Face-invariance from a contract coloring. -/
theorem CcColoring.face_invariant {G : Hypermap} {cc : Finset G.Dart} {k : G.Dart → Color}
    (h : CcColoring cc k) : ∀ x, k (G.face x) = k x := h.2.2

-- Coq: coloring.v – a Coloring yields a CcColoring when no dart touches cc
/-- A coloring is a contract coloring for any cc disjoint from every dart and
    its edge-image. The hypothesis is strong (it forces cc = ∅ in practice);
    the main use-case is `coloring_to_cc_empty`. -/
theorem coloring_to_cc_of_disjoint {G : Hypermap} {cc : Finset G.Dart} {k : G.Dart → Color}
    (hCol : Coloring k)
    (hdisj : ∀ x, x ∉ cc ∧ G.edge x ∉ cc) : CcColoring cc k :=
  ⟨fun x _ => hCol.edge_distinct x,
   fun x h => absurd h (not_or.mpr (hdisj x)),
   hCol.face_invariant⟩

/-! ## Ring traces -/

/-- A ring trace: there exists a proper coloring whose restriction to
    the ring r produces the edge trace et. -/
def RingTrace (r : List G.Dart) (et : List Color) : Prop :=
  ∃ k : G.Dart → Color, Coloring k ∧ et = Color.trace (r.map k)

/-- A contract ring trace. -/
def CcRingTrace (cc : Finset G.Dart) (r : List G.Dart) (et : List Color) : Prop :=
  ∃ k : G.Dart → Color, CcColoring cc k ∧ et = Color.trace (r.map k)

-- Coq: coloring.v (ring trace length)
/-- The length of a ring trace equals the length of the ring. -/
theorem RingTrace_length {r : List G.Dart} {et : List Color}
    (h : RingTrace r et) : et.length = r.length := by
  obtain ⟨k, _, rfl⟩ := h
  rw [Color.length_trace, List.length_map]

-- Coq: coloring.v (cc ring trace length)
/-- The length of a contract ring trace equals the length of the ring. -/
theorem CcRingTrace_length {cc : Finset G.Dart} {r : List G.Dart} {et : List Color}
    (h : CcRingTrace cc r et) : et.length = r.length := by
  obtain ⟨k, _, rfl⟩ := h
  rw [Color.length_trace, List.length_map]

-- Coq: coloring.v (empty contract weakening)
/-- An empty contract: a coloring is always a cc-coloring for the empty set. -/
theorem coloring_to_cc_empty {k : G.Dart → Color} (h : Coloring k) :
    CcColoring (∅ : Finset G.Dart) k := by
  obtain ⟨hkE, hkF⟩ := h
  refine ⟨?_, ?_, hkF⟩
  · intro x _; exact hkE x
  · intro x hx
    rcases hx with hx | hx <;> exact absurd hx (Finset.notMem_empty _)

/-- Every ring-trace is a cc-ring-trace for the empty contract. -/
theorem RingTrace_to_CcRingTrace_empty {r : List G.Dart} {et : List Color}
    (h : RingTrace r et) : CcRingTrace (∅ : Finset G.Dart) r et := by
  obtain ⟨k, hk, heq⟩ := h
  exact ⟨k, coloring_to_cc_empty hk, heq⟩

/-- A ring trace is non-empty when the ring is non-empty. -/
theorem RingTrace_ne_nil_of_ne_nil {r : List G.Dart} {et : List Color}
    (h : RingTrace r et) (hr : r ≠ []) : et ≠ [] := by
  intro het
  have := RingTrace_length h
  rw [het] at this
  simp at this
  exact hr (List.eq_nil_iff_length_eq_zero.mpr this.symm)

/-! ## Minimal counter-example -/

/-- A minimal counter-example to the four color theorem for hypermaps:
    a non-four-colorable planar bridgeless plain precubic hypermap,
    such that all strictly smaller such hypermaps are four-colorable. -/
def MinimalCounterExample (G : Hypermap) : Prop :=
  ¬ FourColorable G ∧
  Planar G ∧
  Bridgeless G ∧
  Plain G ∧
  Precubic G ∧
  (∀ H : Hypermap.{0},
    Fintype.card H.Dart < Fintype.card G.Dart →
    Planar H → Bridgeless H → Plain H → Precubic H →
    FourColorable H)

/-- Extract non-four-colorability from a minimal counter-example. -/
theorem MinimalCounterExample.not_four_colorable {G : Hypermap}
    (h : MinimalCounterExample G) : ¬ FourColorable G := h.1

/-- Extract planarity from a minimal counter-example. -/
theorem MinimalCounterExample.planar {G : Hypermap}
    (h : MinimalCounterExample G) : Planar G := h.2.1

/-- Extract bridgelessness from a minimal counter-example. -/
theorem MinimalCounterExample.bridgeless {G : Hypermap}
    (h : MinimalCounterExample G) : Bridgeless G := h.2.2.1

/-- Extract plainness from a minimal counter-example. -/
theorem MinimalCounterExample.plain {G : Hypermap}
    (h : MinimalCounterExample G) : Plain G := h.2.2.2.1

/-- Extract precubicity from a minimal counter-example. -/
theorem MinimalCounterExample.precubic {G : Hypermap}
    (h : MinimalCounterExample G) : Precubic G := h.2.2.2.2.1

/-! ## Good ring arity -/

/-- The face arity of dart x is in the range {3, 4, 5, 6}.
    Corresponds to Coq `good_ring_arity` (coloring.v:395):
      Definition good_ring_arity (x : G) : bool := pred4 3 4 5 6 (order face x).
-/
def GoodRingArity (G : Hypermap) (x : G.Dart) : Prop :=
  arity G x = 3 ∨ arity G x = 4 ∨ arity G x = 5 ∨ arity G x = 6

/-! ## Radius 2 -/

/-- Two darts x, y are at radius 2 within A if there exists a common
    neighbor z ∈ A that is adjacent to both x and y.
    Corresponds to Coq `at_radius2` (coloring.v:419-420):
      Definition at_radius2 := [rel x y | ~~ [disjoint adj y & [predI adj x & A]]].
    which unfolds to: ∃ z, adj y z ∧ adj x z ∧ A z. -/
def AtRadius2 (G : Hypermap) (A : G.Dart → Prop) (x y : G.Dart) : Prop :=
  ∃ z : G.Dart, A z ∧ adj G x z ∧ adj G y z

/-- A predicate A has radius 2 if there is a center x ∈ A such that every
    y ∈ A is at radius 2 from x within A.
    Corresponds to Coq `radius2` (coloring.v:427):
      Definition radius2 := ~~ [disjoint A & [pred x | A \subset at_radius2 x]].
    i.e., ∃ x, A x ∧ ∀ y, A y → at_radius2 x y. -/
def Radius2 (G : Hypermap) (A : G.Dart → Prop) : Prop :=
  ∃ x : G.Dart, A x ∧ ∀ y : G.Dart, A y → AtRadius2 G A x y

/-! ## Sparse -/

/-- A sequence of darts is sparse (node-simple): no two darts belong to
    the same node orbit.
    Corresponds to Coq `sparse` (coloring.v:444):
      Definition sparse (p : seq G) := simple (p : seq (permF G)).
    In the permF (face-adjusted) structure, face-connectivity becomes
    node-connectivity, so "simple under permF" means "node-simple". -/
def Sparse (p : List G.Dart) : Prop :=
  p.Pairwise (fun x y => ¬ cnode G x y)

/-- Node-connectivity is symmetric: if y is reachable from x by iterating
    node, then x is reachable from y (since node is a permutation on a
    finite type). -/
theorem cnode_symm (x y : G.Dart) : cnode G x y → cnode G y x := by
  intro ⟨n, hn⟩
  have hper : x ∈ Function.periodicPts G.node :=
    node_injective.mem_periodicPts x
  have hpos := Function.minimalPeriod_pos_of_mem_periodicPts hper
  have hmp : G.node^[Function.minimalPeriod G.node x] x = x :=
    Function.isPeriodicPt_minimalPeriod G.node x
  set k := Function.minimalPeriod G.node x with hk_def
  have hlt : n % k < k := Nat.mod_lt n hpos
  use k - n % k
  have step1 : G.node^[n % k] x = G.node^[n] x :=
    Function.IsPeriodicPt.iterate_mod_apply hmp n
  rw [← hn]
  have step2 : G.node^[k - n % k] (G.node^[n] x) = x := by
    rw [← step1, ← Function.iterate_add_apply]
    have : k - n % k + n % k = k := by omega
    rw [this]; exact hmp
  exact step2

/-- Sparse cons: a cons list is sparse iff the head is not node-connected
    to any element of the tail, and the tail is sparse.
    Corresponds to Coq `sparse_cons` (coloring.v:446). -/
theorem sparse_cons (x : G.Dart) (p : List G.Dart) :
    Sparse (x :: p) ↔ (∀ y ∈ p, ¬ cnode G x y) ∧ Sparse p := by
  simp [Sparse, List.pairwise_cons]

/-- Sparse is invariant under cyclic rotation of the list (append-commute).
    Corresponds to Coq `sparse_catC` (coloring.v:449):
      Lemma sparse_catC p1 p2 : sparse (p1 ++ p2) = sparse (p2 ++ p1). -/
theorem sparse_append_comm (p1 p2 : List G.Dart) :
    Sparse (p1 ++ p2) ↔ Sparse (p2 ++ p1) := by
  simp only [Sparse, List.pairwise_append]
  constructor <;> intro ⟨h1, h2, h3⟩ <;> refine ⟨h2, h1, ?_⟩ <;>
    intro a ha b hb hab <;>
    exact h3 b hb a ha (cnode_symm a b hab)

/-- Nothing is in a sparse empty list. -/
theorem sparse_nil : Sparse ([] : List G.Dart) := List.Pairwise.nil

/-- Sparse implies duplicate-free (since each element is cnode-related to
    itself and the sparse predicate is ¬ cnode). -/
theorem sparse_nodup {p : List G.Dart} (hs : Sparse p) : p.Nodup := by
  induction p with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    rcases (sparse_cons x xs).mp hs with ⟨hhead, htail⟩
    refine List.Pairwise.cons ?_ (ih htail)
    intro y hy heq
    exact hhead y hy (heq ▸ cnode_refl x)

/-- Singleton lists are sparse. -/
theorem sparse_singleton (x : G.Dart) : Sparse [x] :=
  List.pairwise_singleton _ _

/-! ## Face orbit -/

/-- The face orbit of a dart x, as a Finset. This is the set of all darts
    reachable from x by iterating G.face. -/
def faceOrbit (G : Hypermap) (x : G.Dart) : Finset G.Dart :=
  Finset.univ.filter (fun y => cface G x y)

theorem mem_faceOrbit (x y : G.Dart) :
    y ∈ faceOrbit G x ↔ cface G x y := by
  simp [faceOrbit, Finset.mem_filter]

/-! ## Triad -/

/-- A dart x is a triad for the sequence p if at least 3 faces in the face
    orbit of x have an edge landing in the face band of p, and not all
    elements of p are adjacent to x.
    Corresponds to Coq `triad` (coloring.v:458-460):
      Definition triad (p : seq G) :=
        let adjp y := fband p (edge y) in
        [pred x | (2 < count adjp (orbit face x)) && ~~ (p \subset adj x)].
-/
def Triad (G : Hypermap) (p : List G.Dart) (x : G.Dart) : Prop :=
  2 < ((faceOrbit G x).filter (fun z => fband G p (G.edge z))).card ∧
  ¬ (∀ y ∈ p, adj G y x)

/-! ## Embeddability -/

/-- A configuration is embeddable with perimeter ring r if it is planar,
    bridgeless, connected, plain, and r-quasicubic for the simple N-cycle r,
    and additionally all ring darts have good ring arity and the kernel
    has radius 2.
    Corresponds to Coq `embeddable` record (coloring.v:438-442):
      Record embeddable : Prop := Embeddable {
        embeddable_base :> scycle_planar_bridgeless_plain_quasicubic_connected r;
        embeddable_ring : all good_ring_arity r;
        embeddable_kernel : radius2 (kernel r)
      }. -/
def Embeddable (r : List G.Dart) : Prop :=
  Planar G ∧
  Bridgeless G ∧
  Connected G ∧
  Plain G ∧
  Quasicubic G (r.toFinset) ∧
  Srcycle G r ∧
  (∀ x ∈ r, GoodRingArity G x) ∧
  Radius2 G (kernel G r)

/-! ## C-reducibility -/

/-- A valid contract for ring r: the edge-closure of cc is disjoint from r,
    sparse, has size between 1 and 4, and if size is 4, there exists a
    kernel triad.
    Corresponds to Coq `valid_contract` record (coloring.v:462-468):
      Record valid_contract : Prop := ValidContract {
        valid_contract_is_off_ring : [disjoint r & insertE cc];
        valid_contract_is_sparse : sparse (insertE cc);
        valid_contract_size : pred4 1 2 3 4 (size cc);
        valid_contract_triad :
           size cc = 4 -> ~~ [disjoint kernel r & triad (insertE cc)]
      }. -/
def ValidContract (r : List G.Dart) (cc : Finset G.Dart) : Prop :=
  Disjoint r.toFinset (insertE G cc.toList).toFinset ∧
  Sparse (insertE G cc.toList) ∧
  (1 ≤ cc.card ∧ cc.card ≤ 4) ∧
  (cc.card = 4 → ∃ x, kernel G r x ∧ Triad G (insertE G cc.toList) x)

/-- Kempe coclosure of the ring-trace predicate at the edge-trace `et`:
    every Kempe-closed superset of the ring-trace predicate that contains `et`
    must intersect it. Delegates to `FourColor.Chromogram.KempeCoclosure`
    applied to the ring-trace predicate of the *reversed* ring (matching
    Coq's `ring_trace (rev r)` in the definition of `C_reducible`).
    Corresponds to `Kempe_coclosure (ring_trace (rev r))` in coloring.v:472-473. -/
def KempeCoclosure (r : List G.Dart) (et : List Color) : Prop :=
  FourColor.Chromogram.KempeCoclosure (fun et' => RingTrace (G := G) r.reverse et') et

/-- C-reducibility: assuming G is a configuration with ring r, G is
    C-reducible with contract cc if cc is valid and any contract ring trace
    for cc is in the Kempe coclosure of the set of ring traces of colorings.
    Corresponds to Coq `C_reducible` record (coloring.v:470-474):
      Record C_reducible : Prop := Creducible {
        C_reducible_base :> valid_contract;
        C_reducible_coclosure : forall et : colseq,
          cc_ring_trace cc (rev r) et -> Kempe_coclosure (ring_trace (rev r)) et
      }. -/
def CReducible (r : List G.Dart) (cc : Finset G.Dart) : Prop :=
  ValidContract r cc ∧
  ∀ et : List Color, CcRingTrace cc (r.reverse) et → KempeCoclosure r et

/-! ## Decidability of four-colorability -/

/-- Four-colorability is decidable for finite hypermaps. -/
instance (G : Hypermap) : Decidable (FourColorable G) :=
  Classical.dec _

/-! ## Colorable existential builders -/

theorem FourColorable.exists_coloring {G : Hypermap} (h : FourColorable G) :
    ∃ k : G.Dart → Color, Coloring k := h

theorem FourColorable.intro {G : Hypermap} {k : G.Dart → Color} (hk : Coloring k) :
    FourColorable G := ⟨k, hk⟩

theorem GraphFourColorable.exists_coloring {G : Hypermap}
    (h : GraphFourColorable G) :
    ∃ k : G.Dart → Color, GraphColoring k := h

theorem GraphFourColorable.intro {G : Hypermap} {k : G.Dart → Color}
    (hk : GraphColoring k) : GraphFourColorable G := ⟨k, hk⟩

theorem CcColorable.exists_coloring {G : Hypermap} {cc : Finset G.Dart}
    (h : CcColorable cc) : ∃ k : G.Dart → Color, CcColoring cc k := h

theorem CcColorable.intro {G : Hypermap} {cc : Finset G.Dart} {k : G.Dart → Color}
    (hk : CcColoring cc k) : CcColorable cc := ⟨k, hk⟩

/-- `FourColorable G` from `FourColorable (mirror G)`. -/
theorem FourColorable.of_mirror {G : Hypermap}
    (h : FourColorable (mirror G)) : FourColorable G :=
  colorable_mirror h

/-! ## Coloring / GraphColoring constructors -/

theorem Coloring.mk' {G : Hypermap} {k : G.Dart → Color}
    (hkE : ∀ x, k (G.edge x) ≠ k x) (hkF : ∀ x, k (G.face x) = k x) : Coloring k :=
  ⟨hkE, hkF⟩

theorem Coloring.iff_and {G : Hypermap} {k : G.Dart → Color} :
    Coloring k ↔ (∀ x, k (G.edge x) ≠ k x) ∧ (∀ x, k (G.face x) = k x) := Iff.rfl

theorem GraphColoring.mk' {G : Hypermap} {k : G.Dart → Color}
    (hkE : ∀ x, k (G.edge x) ≠ k x) (hkN : ∀ x, k (G.node x) = k x) : GraphColoring k :=
  ⟨hkE, hkN⟩

theorem GraphColoring.iff_and {G : Hypermap} {k : G.Dart → Color} :
    GraphColoring k ↔ (∀ x, k (G.edge x) ≠ k x) ∧ (∀ x, k (G.node x) = k x) := Iff.rfl

/-! ## Convenience projection aliases -/

theorem Coloring.proper_edge {G : Hypermap} {k : G.Dart → Color}
    (h : Coloring k) (x : G.Dart) : k (G.edge x) ≠ k x := h.1 x

theorem Coloring.face_eq {G : Hypermap} {k : G.Dart → Color}
    (h : Coloring k) (x : G.Dart) : k (G.face x) = k x := h.2 x

/-- A `Coloring` differs across a single edge step. -/
theorem Coloring.edge_ne {G : Hypermap} {k : G.Dart → Color}
    (h : Coloring k) (x : G.Dart) : k (G.edge x) ≠ k x :=
  h.proper_edge x

/-- If two darts have the same color, they are not related by edge. -/
theorem Coloring.eq_imp_not_edge {G : Hypermap} {k : G.Dart → Color}
    (h : Coloring k) {x y : G.Dart} (hk : k x = k y) : G.edge x ≠ y := by
  intro he
  exact h.proper_edge x (he ▸ hk).symm

theorem GraphColoring.proper_edge {G : Hypermap} {k : G.Dart → Color}
    (h : GraphColoring k) (x : G.Dart) : k (G.edge x) ≠ k x := h.1 x

theorem GraphColoring.node_eq {G : Hypermap} {k : G.Dart → Color}
    (h : GraphColoring k) (x : G.Dart) : k (G.node x) = k x := h.2 x

/-- A `GraphColoring` differs across a single edge step. -/
theorem GraphColoring.edge_ne {G : Hypermap} {k : G.Dart → Color}
    (h : GraphColoring k) (x : G.Dart) : k (G.edge x) ≠ k x :=
  h.proper_edge x

/-- If two darts have the same color, they are not related by edge in a GraphColoring. -/
theorem GraphColoring.eq_imp_not_edge {G : Hypermap} {k : G.Dart → Color}
    (h : GraphColoring k) {x y : G.Dart} (hk : k x = k y) : G.edge x ≠ y := by
  intro he
  exact h.proper_edge x (he ▸ hk).symm

theorem Coloring.face_iter {G : Hypermap} {k : G.Dart → Color}
    (h : Coloring k) (n : ℕ) (x : G.Dart) : k ((G.face^[n]) x) = k x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', h.face_eq]; exact ih

theorem Coloring.face_iter_symm {G : Hypermap} {k : G.Dart → Color}
    (h : Coloring k) (n : ℕ) (x : G.Dart) : k x = k ((G.face^[n]) x) :=
  (Coloring.face_iter h n x).symm

/-- `Coloring.face_iter` at n=1 reduces to `Coloring.face_eq`. -/
theorem Coloring.face_iter_one {G : Hypermap} {k : G.Dart → Color}
    (h : Coloring k) (x : G.Dart) : k ((G.face^[1]) x) = k x := h.face_iter 1 x

/-- A `Coloring` value is constant on an entire `cface` orbit (symmetric variant). -/
theorem Coloring.cface_iff_eq {G : Hypermap} {k : G.Dart → Color}
    (h : Coloring k) {x y : G.Dart} (hc : Hypermap.cface G x y) : k x = k y :=
  (Coloring.cface h hc).symm

theorem GraphColoring.node_iter {G : Hypermap} {k : G.Dart → Color}
    (h : GraphColoring k) (n : ℕ) (x : G.Dart) : k ((G.node^[n]) x) = k x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', h.node_eq]; exact ih

theorem GraphColoring.node_iter_symm {G : Hypermap} {k : G.Dart → Color}
    (h : GraphColoring k) (n : ℕ) (x : G.Dart) : k x = k ((G.node^[n]) x) :=
  (GraphColoring.node_iter h n x).symm

/-- `GraphColoring.node_iter` at n=1 reduces to `GraphColoring.node_eq`. -/
theorem GraphColoring.node_iter_one {G : Hypermap} {k : G.Dart → Color}
    (h : GraphColoring k) (x : G.Dart) : k ((G.node^[1]) x) = k x := h.node_iter 1 x

/-- A `Coloring` value at face^[n] x equals value at face^[m] x for any m,n. -/
theorem Coloring.face_iter_eq_iter {G : Hypermap} {k : G.Dart → Color}
    (h : Coloring k) (m n : ℕ) (x : G.Dart) :
    k ((G.face^[m]) x) = k ((G.face^[n]) x) := by
  rw [Coloring.face_iter h m, Coloring.face_iter h n]

/-- A `GraphColoring` value at node^[n] x equals value at node^[m] x. -/
theorem GraphColoring.node_iter_eq_iter {G : Hypermap} {k : G.Dart → Color}
    (h : GraphColoring k) (m n : ℕ) (x : G.Dart) :
    k ((G.node^[m]) x) = k ((G.node^[n]) x) := by
  rw [GraphColoring.node_iter h m, GraphColoring.node_iter h n]

/-- Face-invariance projection for CcColoring. -/
theorem CcColoring.face_eq {G : Hypermap} {cc : Finset G.Dart} {k : G.Dart → Color}
    (h : CcColoring cc k) (x : G.Dart) : k (G.face x) = k x :=
  h.face_invariant x

/-- A `GraphColoring` on `G` gives a `Coloring` on `dual G`. -/
theorem Coloring.of_GraphColoring_dual {G : Hypermap} {k : G.Dart → Color}
    (h : GraphColoring k) : @Coloring (dual G) k := coloring_dual.mpr h

/-! ## GraphColoring orbit invariance -/

/-- A GraphColoring is constant on cnode-orbits. -/
theorem GraphColoring.cnode {G : Hypermap} {k : G.Dart → Color}
    (h : GraphColoring k) {x y : G.Dart} (hc : cnode G x y) : k y = k x := by
  obtain ⟨n, rfl⟩ := hc
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', h.node_invariant]
    exact ih

/-- A `GraphColoring` is constant on cnode-orbits (n-step variant). -/
theorem GraphColoring.cnode_iff_eq {G : Hypermap} {k : G.Dart → Color}
    (h : GraphColoring k) {x y : G.Dart} (hc : Hypermap.cnode G x y) : k x = k y :=
  (GraphColoring.cnode h hc).symm

/-- A GraphColoring is constant on cnode-orbits (Coloring-namespace alias). -/
theorem Coloring.cnode_invariant_of_GraphColoring {G : Hypermap} {k : G.Dart → Color}
    (h : GraphColoring k) {x y : G.Dart} (hc : cnode G x y) : k y = k x :=
  GraphColoring.cnode h hc

/-- A graph coloring induces a coloring of the dual hypermap. -/
theorem dual_Coloring_of_GraphColoring {G : Hypermap} {k : G.Dart → Color}
    (h : GraphColoring k) : @Coloring (dual G) k :=
  coloring_dual.mpr h

/-- A coloring of the dual hypermap induces a graph coloring. -/
theorem GraphColoring_of_dual_Coloring {G : Hypermap} {k : G.Dart → Color}
    (h : @Coloring (dual G) k) : GraphColoring k :=
  coloring_dual.mp h

/-- If the dual hypermap is four-colorable, then G is graph-four-colorable. -/
theorem GraphFourColorable.of_FourColorable_dual {G : Hypermap}
    (h : FourColorable (dual G)) : GraphFourColorable G := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, GraphColoring_of_dual_Coloring hk⟩

/-- If G is graph-four-colorable, then the dual hypermap is four-colorable. -/
theorem FourColorable.of_GraphFourColorable_dual {G : Hypermap}
    (h : GraphFourColorable G) : FourColorable (dual G) :=
  four_colorable_dual.mpr h

/-- A coloring of (mirror G).Dart is also a coloring of G.Dart. -/
theorem mirror_Coloring (G : Hypermap) {k : G.Dart → Color}
    (h : @Coloring (mirror G) k) : Coloring k := coloring_mirror h

end Hypermap
