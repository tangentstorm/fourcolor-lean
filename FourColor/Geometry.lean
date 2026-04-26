/-
Copyright (c) 2006-2018 Microsoft Corporation and Inria (Coq version).
Lean 4 port of the Four Color Theorem formalization.

The geometrical interpretation of hypermap: bridgeless, plain, cubic,
and related properties used throughout the Four Color Theorem proof.
-/
import FourColor.Hypermap

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

/-! ================================================================
    Ported supporting lemmas from `geometry.v` (rocq-community/fourcolor).
    Each lemma is tagged with the original Coq name and line reference.
    ================================================================ -/

variable {G}

/-! ### Orbit symmetry helper

A reusable lemma: on a finite type, iteration orbits of an injective
function are symmetric. Used for `cface_sym`, `cedge_sym`, `cnode_sym`. -/

private theorem iterate_sym {α : Type*} [Finite α] {f : α → α}
    (hf : Function.Injective f) {x y : α} (h : ∃ n : ℕ, f^[n] x = y) :
    ∃ m : ℕ, f^[m] y = x := by
  obtain ⟨n, rfl⟩ := h
  have hpos := Function.minimalPeriod_pos_of_mem_periodicPts
    (Function.Injective.mem_periodicPts hf x)
  set p := Function.minimalPeriod f x
  refine ⟨p - n % p, ?_⟩
  rw [← Function.iterate_add_apply,
      ← Function.iterate_mod_minimalPeriod_eq (f := f) (x := x)]
  have hdvd : p ∣ (p - n % p + n) := by
    refine ⟨1 + n / p, ?_⟩
    zify [(Nat.mod_lt n hpos).le, Nat.mod_le n p]
    linarith [Nat.div_add_mod n p]
  rw [Nat.mod_eq_zero_of_dvd hdvd]
  simp

/-! ### 1. `insertE` lemmas (geometry.v:777–802) -/

-- Coq: size_insertE in geometry.v:777
theorem length_insertE (p : List G.Dart) :
    (insertE G p).length = 2 * p.length := by
  induction p with
  | nil => rfl
  | cons x xs ih => simp [insertE, List.flatMap_cons]; omega

-- Coq: insertE_cat in geometry.v:802
theorem insertE_append (p q : List G.Dart) :
    insertE G (p ++ q) = insertE G p ++ insertE G q := by
  simp [insertE, List.flatMap_append]

/-- `insertE` on the empty list is empty. -/
@[simp] theorem insertE_nil : insertE G ([] : List G.Dart) = [] := rfl

/-- `insertE` unfolds on a cons: prepend `x` and `edge x` before the recursive result. -/
@[simp] theorem insertE_cons (x : G.Dart) (p : List G.Dart) :
    insertE G (x :: p) = x :: G.edge x :: insertE G p := by
  simp [insertE, List.flatMap_cons]

/-- Every element of `p` belongs to `insertE G p`. -/
theorem mem_insertE_self (p : List G.Dart) {x : G.Dart}
    (h : x ∈ p) : x ∈ insertE G p := by
  induction p with
  | nil => simp at h
  | cons y ys ih =>
    rw [insertE_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · exact List.mem_cons.mpr (Or.inl rfl)
    · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (ih h'))))

/-- For every element of `p`, its edge image belongs to `insertE G p`. -/
theorem mem_insertE_edge (p : List G.Dart) {x : G.Dart}
    (h : x ∈ p) : G.edge x ∈ insertE G p := by
  induction p with
  | nil => simp at h
  | cons y ys ih =>
    rw [insertE_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (ih h'))))

/-! ### Unfolding aliases for `cface` / `cedge` / `cnode` -/

theorem cface_iff_exists (G : Hypermap) (x y : G.Dart) :
    cface G x y ↔ ∃ n : ℕ, G.face^[n] x = y := Iff.rfl

theorem cedge_iff_exists (G : Hypermap) (x y : G.Dart) :
    cedge G x y ↔ ∃ n : ℕ, G.edge^[n] x = y := Iff.rfl

theorem cnode_iff_exists (G : Hypermap) (x y : G.Dart) :
    cnode G x y ↔ ∃ n : ℕ, G.node^[n] x = y := Iff.rfl

/-! ### 2. `cface` / `cedge` / `cnode` reflexivity (geometry.v:~145) -/

-- Coq: connect0 (specialized)
theorem cface_refl (x : G.Dart) : cface G x x :=
  ⟨0, rfl⟩

theorem cedge_refl (x : G.Dart) : cedge G x x :=
  ⟨0, rfl⟩

theorem cnode_refl (x : G.Dart) : cnode G x x :=
  ⟨0, rfl⟩

/-! ### 3. Transitivity -/

-- Coq: connect_trans (specialized)
theorem cface_trans {x y z : G.Dart} (h₁ : cface G x y) (h₂ : cface G y z) :
    cface G x z := by
  obtain ⟨m, rfl⟩ := h₁
  obtain ⟨n, rfl⟩ := h₂
  exact ⟨n + m, by rw [Function.iterate_add_apply]⟩

theorem cedge_trans {x y z : G.Dart} (h₁ : cedge G x y) (h₂ : cedge G y z) :
    cedge G x z := by
  obtain ⟨m, rfl⟩ := h₁
  obtain ⟨n, rfl⟩ := h₂
  exact ⟨n + m, by rw [Function.iterate_add_apply]⟩

theorem cnode_trans {x y z : G.Dart} (h₁ : cnode G x y) (h₂ : cnode G y z) :
    cnode G x z := by
  obtain ⟨m, rfl⟩ := h₁
  obtain ⟨n, rfl⟩ := h₂
  exact ⟨n + m, by rw [Function.iterate_add_apply]⟩

/-! ### 4. Symmetry (geometry.v: same_connect_rev / fconnect_sym etc.) -/

-- Coq: cfaceC (symmetry of cface)
theorem cface_sym {x y : G.Dart} (h : cface G x y) : cface G y x :=
  iterate_sym face_injective h

theorem cedge_sym {x y : G.Dart} (h : cedge G x y) : cedge G y x :=
  iterate_sym edge_injective h

theorem cnode_sym {x y : G.Dart} (h : cnode G x y) : cnode G y x :=
  iterate_sym node_injective h

@[simp] theorem cface_comm (G : Hypermap) (x y : G.Dart) : cface G x y ↔ cface G y x :=
  ⟨cface_sym, cface_sym⟩

@[simp] theorem cedge_comm (G : Hypermap) (x y : G.Dart) : cedge G x y ↔ cedge G y x :=
  ⟨cedge_sym, cedge_sym⟩

@[simp] theorem cnode_comm (G : Hypermap) (x y : G.Dart) : cnode G x y ↔ cnode G y x :=
  ⟨cnode_sym, cnode_sym⟩

/-! ### 5. Arity lemmas (geometry.v:145–161) -/

private theorem minimalPeriod_iterate {α : Type*} [Finite α] {f : α → α}
    (hf : Function.Injective f) (n : ℕ) (x : α) :
    Function.minimalPeriod f (f^[n] x) = Function.minimalPeriod f x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply,
        Function.minimalPeriod_apply (Function.Injective.mem_periodicPts hf _), ih]

-- Coq: arity_face in geometry.v:155
theorem arity_face (x : G.Dart) : arity G (G.face x) = arity G x := by
  simp only [arity, orderOf]
  exact Function.minimalPeriod_apply (Function.Injective.mem_periodicPts face_injective x)

-- Coq: arity_iter_face in geometry.v:148
theorem arity_iter_face (n : ℕ) (x : G.Dart) :
    arity G (G.face^[n] x) = arity G x := by
  simp only [arity, orderOf]
  exact minimalPeriod_iterate face_injective n x

-- Coq: arity_cface in geometry.v:158
theorem arity_cface {x y : G.Dart} (h : cface G x y) :
    arity G x = arity G y := by
  obtain ⟨n, rfl⟩ := h
  exact (arity_iter_face n x).symm

/-! ### 6. Bridgeless unfolding (geometry.v:88) -/

-- Coq: bridgeless_cface in geometry.v:88
theorem bridgeless_not_cface (hB : Bridgeless G) (x : G.Dart) :
    ¬ cface G x (G.edge x) :=
  hB x

/-! ### 7. `fband` lemmas (geometry.v:270–304) -/

-- Coq: fbandF in geometry.v:~270
theorem fband_nil (x : G.Dart) : ¬ fband G [] x := by
  simp [fband]

-- Coq: fband_cons in geometry.v
theorem fband_cons (y : G.Dart) (p : List G.Dart) (x : G.Dart) :
    fband G (y :: p) x ↔ cface G x y ∨ fband G p x := by
  constructor
  · rintro ⟨z, hz_mem, hz_face⟩
    rcases List.mem_cons.mp hz_mem with rfl | hz_mem
    · exact Or.inl hz_face
    · exact Or.inr ⟨z, hz_mem, hz_face⟩
  · rintro (h | ⟨z, hz_mem, hz_face⟩)
    · exact ⟨y, List.mem_cons.mpr (Or.inl rfl), h⟩
    · exact ⟨z, List.mem_cons.mpr (Or.inr hz_mem), hz_face⟩

-- Coq: fband_cat in geometry.v:~290
theorem fband_append (p q : List G.Dart) (x : G.Dart) :
    fband G (p ++ q) x ↔ fband G p x ∨ fband G q x := by
  constructor
  · rintro ⟨z, hz_mem, hz_face⟩
    rcases List.mem_append.mp hz_mem with hz_mem | hz_mem
    · exact Or.inl ⟨z, hz_mem, hz_face⟩
    · exact Or.inr ⟨z, hz_mem, hz_face⟩
  · rintro (⟨z, hz_mem, hz_face⟩ | ⟨z, hz_mem, hz_face⟩)
    · exact ⟨z, List.mem_append.mpr (Or.inl hz_mem), hz_face⟩
    · exact ⟨z, List.mem_append.mpr (Or.inr hz_mem), hz_face⟩

-- Coq: ring_fband (partial) – cface implies fband membership
theorem fband_cface {p : List G.Dart} {x y : G.Dart}
    (hy : y ∈ p) (hf : cface G x y) : fband G p x :=
  ⟨y, hy, hf⟩

-- fband is monotone in the list
theorem fband_subset {p q : List G.Dart} (hsub : ∀ x, x ∈ p → x ∈ q) :
    ∀ x, fband G p x → fband G q x := by
  intro x ⟨y, hy_mem, hy_face⟩
  exact ⟨y, hsub y hy_mem, hy_face⟩

/-! ### 8. `Simple` (face-simple) lemmas (geometry.v:287–327) -/

-- Coq: simple0 in geometry.v:~287
theorem simple_nil : Simple G [] :=
  List.Pairwise.nil

-- Coq: simple_cons in geometry.v
theorem simple_cons (x : G.Dart) (p : List G.Dart) :
    Simple G (x :: p) ↔ (∀ y ∈ p, ¬ cface G x y) ∧ Simple G p := by
  exact List.pairwise_cons

@[simp] theorem Simple.nil : Simple G ([] : List G.Dart) := List.Pairwise.nil

/-- `Simple G []` is trivially true (vacuous). -/
@[simp] theorem Simple.nil_iff (G : Hypermap) : Simple G ([] : List G.Dart) ↔ True :=
  iff_true_intro Simple.nil

theorem Simple.cons_iff (x : G.Dart) (p : List G.Dart) :
    Simple G (x :: p) ↔ (∀ y ∈ p, ¬ cface G x y) ∧ Simple G p :=
  List.pairwise_cons

theorem Simple.tail {x : G.Dart} {p : List G.Dart}
    (h : Simple G (x :: p)) : Simple G p :=
  ((Simple.cons_iff x p).mp h).2

theorem Simple.head_not_band {x : G.Dart} {p : List G.Dart}
    (h : Simple G (x :: p)) (y : G.Dart) (hy : y ∈ p) : ¬ cface G x y :=
  ((Simple.cons_iff x p).mp h).1 y hy

/-- Membership in tail of a Simple list. -/
theorem Simple.mem_tail_imp_not_cface_head {x : G.Dart} {p : List G.Dart}
    (h : Simple G (x :: p)) {y : G.Dart} (hy : y ∈ p) : ¬ cface G x y :=
  Simple.head_not_band h y hy

/-- A Simple cons is determined by its head condition and tail. -/
theorem Simple.cons_split {x : G.Dart} {p : List G.Dart}
    (h : Simple G (x :: p)) : (∀ y ∈ p, ¬ cface G x y) ∧ Simple G p :=
  (Simple.cons_iff x p).mp h

/-- Construct a face-simple cons from its components. -/
theorem Simple.cons {x : G.Dart} {p : List G.Dart}
    (h₁ : ∀ y ∈ p, ¬ cface G x y) (h₂ : Simple G p) : Simple G (x :: p) :=
  (Simple.cons_iff x p).mpr ⟨h₁, h₂⟩

/-- A two-element list is face-simple iff the two darts are not coface. -/
theorem Simple.pair {x y : G.Dart}
    (h : ¬ cface G x y) : Simple G [x, y] := by
  unfold Simple
  exact List.pairwise_pair.mpr h

/-- The head of a Simple cons doesn't fband the tail. -/
theorem Simple.head_not_fband {x : G.Dart} {p : List G.Dart}
    (h : Simple G (x :: p)) : ¬ fband G p x := by
  rw [Simple.cons_iff] at h
  intro hfb
  obtain ⟨y, hy, hcf⟩ := hfb
  exact h.1 y hy hcf

/-- A list is face-simple iff its head doesn't fband the tail and tail is simple. -/
theorem Simple.cons_iff_fband {x : G.Dart} {p : List G.Dart} :
    Simple G (x :: p) ↔ ¬ fband G p x ∧ Simple G p := by
  rw [Simple.cons_iff x p]
  unfold fband
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, h₂⟩
    rintro ⟨y, hy, hcf⟩
    exact h₁ y hy hcf
  · rintro ⟨h₁, h₂⟩
    refine ⟨?_, h₂⟩
    intro y hy hcf
    exact h₁ ⟨y, hy, hcf⟩

-- Coq: simple_cat / simple_catC in geometry.v
theorem simple_append (p q : List G.Dart) :
    Simple G (p ++ q) ↔ Simple G p ∧ Simple G q ∧
      (∀ x ∈ p, ∀ y ∈ q, ¬ cface G x y) := by
  exact List.pairwise_append

/-- Construct a face-simple list from two simple lists with no cross-face overlap. -/
theorem Simple.append (p q : List G.Dart)
    (hp : Simple G p) (hq : Simple G q)
    (hpq : ∀ x ∈ p, ∀ y ∈ q, ¬ cface G x y) : Simple G (p ++ q) :=
  (simple_append p q).mpr ⟨hp, hq, hpq⟩

/-- The left part of a face-simple append is face-simple. -/
theorem Simple.append_left {p q : List G.Dart} (h : Simple G (p ++ q)) : Simple G p :=
  ((simple_append p q).mp h).1

/-- The right part of a face-simple append is face-simple. -/
theorem Simple.append_right {p q : List G.Dart} (h : Simple G (p ++ q)) : Simple G q :=
  ((simple_append p q).mp h).2.1

/-- The pairwise no-cface condition for `Simple.append`. -/
theorem Simple.append_disjoint {p q : List G.Dart} (h : Simple G (p ++ q)) :
    ∀ x ∈ p, ∀ y ∈ q, ¬ cface G x y :=
  ((simple_append p q).mp h).2.2

/-! ### 9. Additional connectivity lemmas -/

-- Coq: cface1 in geometry.v – one-step connectivity
theorem cface_face (x : G.Dart) : cface G x (G.face x) :=
  ⟨1, rfl⟩

theorem cedge_edge (x : G.Dart) : cedge G x (G.edge x) :=
  ⟨1, rfl⟩

theorem cnode_node (x : G.Dart) : cnode G x (G.node x) :=
  ⟨1, rfl⟩

-- cface from iterate
theorem cface_iter_face (n : ℕ) (x : G.Dart) : cface G x (G.face^[n] x) :=
  ⟨n, rfl⟩

theorem cedge_iter_edge (n : ℕ) (x : G.Dart) : cedge G x (G.edge^[n] x) :=
  ⟨n, rfl⟩

theorem cnode_iter_node (n : ℕ) (x : G.Dart) : cnode G x (G.node^[n] x) :=
  ⟨n, rfl⟩

-- Transitive step lemmas: extending an orbit element stays in the orbit.
theorem cface_step_left (x y : G.Dart) (h : cface G x y) : cface G x (G.face y) := by
  obtain ⟨n, rfl⟩ := h; exact ⟨n + 1, by rw [Function.iterate_succ_apply']⟩

theorem cedge_step_left (x y : G.Dart) (h : cedge G x y) : cedge G x (G.edge y) := by
  obtain ⟨n, rfl⟩ := h; exact ⟨n + 1, by rw [Function.iterate_succ_apply']⟩

theorem cnode_step_left (x y : G.Dart) (h : cnode G x y) : cnode G x (G.node y) := by
  obtain ⟨n, rfl⟩ := h; exact ⟨n + 1, by rw [Function.iterate_succ_apply']⟩

theorem cface_iter_step (G : Hypermap) (n : ℕ) (x y : G.Dart)
    (h : cface G x y) : cface G (G.face^[n] x) (G.face^[n] y) := by
  obtain ⟨m, rfl⟩ := h
  refine ⟨m, ?_⟩
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm]

theorem cedge_iter_step (G : Hypermap) (n : ℕ) (x y : G.Dart)
    (h : cedge G x y) : cedge G (G.edge^[n] x) (G.edge^[n] y) := by
  obtain ⟨m, rfl⟩ := h
  refine ⟨m, ?_⟩
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm]

theorem cnode_iter_step (G : Hypermap) (n : ℕ) (x y : G.Dart)
    (h : cnode G x y) : cnode G (G.node^[n] x) (G.node^[n] y) := by
  obtain ⟨m, rfl⟩ := h
  refine ⟨m, ?_⟩
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply, Nat.add_comm]

/-- Append `face^[k]` to a cface chain. -/
theorem cface_iter_extend (G : Hypermap) (x y : G.Dart) (k : ℕ)
    (h : cface G x y) : cface G x (G.face^[k] y) := by
  induction k with
  | zero => exact h
  | succ k ih => exact Function.iterate_succ_apply' G.face k y ▸ cface_step_left x (G.face^[k] y) ih

/-- Append `edge^[k]` to a cedge chain. -/
theorem cedge_iter_extend (G : Hypermap) (x y : G.Dart) (k : ℕ)
    (h : cedge G x y) : cedge G x (G.edge^[k] y) := by
  induction k with
  | zero => exact h
  | succ k ih => exact Function.iterate_succ_apply' G.edge k y ▸ cedge_step_left x (G.edge^[k] y) ih

/-- Append `node^[k]` to a cnode chain. -/
theorem cnode_iter_extend (G : Hypermap) (x y : G.Dart) (k : ℕ)
    (h : cnode G x y) : cnode G x (G.node^[k] y) := by
  induction k with
  | zero => exact h
  | succ k ih => exact Function.iterate_succ_apply' G.node k y ▸ cnode_step_left x (G.node^[k] y) ih

/-! ================================================================
    Batch 2: Additional supporting lemmas from `geometry.v`.
    ================================================================ -/

/-! ### 10. Plain edge characterisation -/

-- Coq: plain_eq / plain_neq in geometry.v
theorem plain_edge_invol (hP : Plain G) (x : G.Dart) : G.edge (G.edge x) = x :=
  (hP x).1

theorem plain_edge_ne (hP : Plain G) (x : G.Dart) : G.edge x ≠ x :=
  (hP x).2

private theorem edge_iter_plain (hP : Plain G) (n : ℕ) (x : G.Dart) :
    G.edge^[n] x = x ∨ G.edge^[n] x = G.edge x := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    rcases ih with h | h <;> rw [h]
    · exact Or.inr rfl
    · rw [plain_edge_invol hP]; exact Or.inl rfl

/-- For a plain map, `cedge x y ↔ x = y ∨ G.edge x = y`. -/
theorem cedge_plain (hP : Plain G) (x y : G.Dart) :
    cedge G x y ↔ x = y ∨ G.edge x = y := by
  constructor
  · rintro ⟨n, rfl⟩
    rcases edge_iter_plain hP n x with h | h <;> [exact Or.inl h.symm; exact Or.inr h.symm]
  · rintro (rfl | rfl)
    · exact cedge_refl x
    · exact cedge_edge x

/-! ### 11. `mem_insertE` (geometry.v:790) -/

-- Coq: mem_insertE in geometry.v:790
/-- For a plain map, `x ∈ insertE p` iff there exists `y ∈ p` with `cedge x y`. -/
theorem mem_insertE (hP : Plain G) (p : List G.Dart) (x : G.Dart) :
    x ∈ insertE G p ↔ ∃ y ∈ p, cedge G x y := by
  simp only [insertE, List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false]
  constructor
  · rintro ⟨a, ha_mem, h | h⟩
    · exact ⟨a, ha_mem, h ▸ cedge_refl a⟩
    · exact ⟨a, ha_mem, h ▸ cedge_sym (cedge_edge a)⟩
  · rintro ⟨a, ha_mem, hcedge⟩
    refine ⟨a, ha_mem, ?_⟩
    rcases (cedge_plain hP x a).mp hcedge with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (by rw [← h, plain_edge_invol hP])

/-! ### 12. `fband_face` (geometry.v:173) -/

-- Coq: fbandF in geometry.v:173
/-- The face band is closed under the face permutation. -/
theorem fband_face (p : List G.Dart) (x : G.Dart) :
    fband G p (G.face x) ↔ fband G p x := by
  constructor
  · rintro ⟨y, hy_mem, hy_face⟩
    exact ⟨y, hy_mem, cface_trans (cface_face x) hy_face⟩
  · rintro ⟨y, hy_mem, hy_face⟩
    exact ⟨y, hy_mem, cface_trans (cface_sym (cface_face x)) hy_face⟩

/-! ### 13. `kernel_face` (geometry.v:189) -/

-- Coq: kernel_face in geometry.v:189
/-- The kernel is closed under the face permutation. -/
theorem kernel_face (p : List G.Dart) (x : G.Dart) :
    kernel G p (G.face x) ↔ kernel G p x := by
  simp only [kernel, fband_face]

/-! ### 14. `kernel_not_mem` (geometry.v:184) -/

-- Coq: kernel_off_ring in geometry.v:184
/-- A dart in the kernel is not in the ring. -/
theorem kernel_not_mem (p : List G.Dart) (x : G.Dart) (h : kernel G p x) : x ∉ p := by
  intro hmem
  exact h ⟨x, hmem, cface_refl x⟩

/-! ### 15. `bridgeless_mirror` — see section 29 below (needs `cface_mirror`). -/

/-! ### 16. `arity_mirror` (geometry.v:161) -/
-- Proved below (section 16b), after the inverse-iteration helpers.

/-! ### 17. `simple_uniq` (geometry.v:205) -/

-- Coq: simple_uniq in geometry.v:205
/-- A face-simple list has no duplicates, because `cface` is reflexive. -/
theorem simple_nodup {p : List G.Dart} (hs : Simple G p) : p.Nodup := by
  have : Std.Irrefl (fun x y : G.Dart => ¬ cface G x y) :=
    ⟨fun x h => h (cface_refl x)⟩
  exact hs.nodup

/-! ### 18. `simple_catC` (geometry.v:327) -/

-- Coq: simple_catC in geometry.v:327
/-- Face-simplicity is invariant under cyclic rotation of the list. -/
theorem simple_append_comm (p q : List G.Dart) :
    Simple G (p ++ q) ↔ Simple G (q ++ p) := by
  simp only [Simple, List.pairwise_append]
  constructor <;> intro ⟨h1, h2, h3⟩ <;> refine ⟨h2, h1, ?_⟩ <;>
    intro a ha b hb hab <;>
    exact h3 b hb a ha (cface_sym hab)

/-! ### 19. `fproj` – face projection (geometry.v:193–197) -/

-- Coq: cface is an equivalence relation, so cface x · = cface y · when cface x y.
theorem cface_iff_of_cface {x y z : G.Dart} (h : cface G x y) :
    cface G x z ↔ cface G y z :=
  ⟨fun hxz => cface_trans (cface_sym h) hxz, fun hyz => cface_trans h hyz⟩

open Classical in
/-- Face projection: pick an element of `p` that is face-connected to `x`,
    defaulting to `x` when none exists.
    Corresponds to Coq `fproj` (geometry.v:193). -/
noncomputable def fproj (G : Hypermap) (p : List G.Dart) (x : G.Dart) : G.Dart :=
  if h : ∃ y ∈ p, cface G x y then h.choose else x

-- Coq: fprojP in geometry.v:195
/-- When `x` is in the face band of `p`, `fproj p x` lies in `p` and is
    face-connected to `x`. -/
theorem fproj_mem {p : List G.Dart} {x : G.Dart} (hx : fband G p x) :
    fproj G p x ∈ p ∧ cface G x (fproj G p x) := by
  unfold fproj
  split
  case isTrue h => exact h.choose_spec
  case isFalse h => exact absurd hx h

private theorem exists_choose_eq {α : Type*} {P Q : α → Prop} (heq : P = Q)
    (hp : ∃ x, P x) (hq : ∃ x, Q x) : hp.choose = hq.choose := by
  subst heq; rfl

-- Coq: fproj_cface in geometry.v:197
/-- Face-connected darts project to the same element of `p`.
    The proof uses propext: when `cface x y`, the predicates `cface x ·` and
    `cface y ·` are extensionally equal, so `Exists.choose` agrees by proof
    irrelevance. -/
theorem fproj_cface {p : List G.Dart} {x y : G.Dart}
    (h : cface G x y) (hx : fband G p x) : fproj G p x = fproj G p y := by
  have hy : fband G p y := by
    obtain ⟨z, hz_mem, hz_face⟩ := hx
    exact ⟨z, hz_mem, cface_trans (cface_sym h) hz_face⟩
  have hpred : (fun z => z ∈ p ∧ cface G x z) = (fun z => z ∈ p ∧ cface G y z) :=
    funext (fun z => by rw [propext (cface_iff_of_cface h)])
  unfold fproj
  split <;> rename_i h1
  · split <;> rename_i h2
    · exact exists_choose_eq hpred h1 h2
    · exact absurd hy h2
  · exact absurd hx h1

/-- fproj of a singleton list. -/
theorem fproj_singleton (G : Hypermap) (x y : G.Dart) (h : cface G y x) :
    fproj G [x] y = x := by
  unfold fproj
  split
  · rename_i h_exists
    rcases h_exists.choose_spec with ⟨hz_mem, _hz_face⟩
    rw [List.mem_singleton] at hz_mem
    exact hz_mem
  · rename_i h_no
    exfalso
    apply h_no
    exact ⟨x, List.mem_singleton.mpr rfl, h⟩

/-- fproj is in the list when fband holds. -/
theorem fproj_mem_self (G : Hypermap) {p : List G.Dart} {x : G.Dart}
    (hx : fband G p x) : fproj G p x ∈ p := (fproj_mem hx).1

/-- fproj is cface-connected to x when fband holds. -/
theorem fproj_cface_self (G : Hypermap) {p : List G.Dart} {x : G.Dart}
    (hx : fband G p x) : cface G x (fproj G p x) := (fproj_mem hx).2

/-! ### 20. `scycle` projection lemmas (geometry.v:212–244) -/

-- Coq: scycle_cycle in geometry.v:212
theorem srcycle_rlink_cycle {r : List G.Dart} (hs : Srcycle G r) :
    ∀ i : Fin r.length,
      rlink G (r.get i)
        (r.get ⟨(i.val + 1) % r.length, Nat.mod_lt _ (by
          have := i.isLt; omega)⟩) := hs.2.2.2

-- Coq: scycle_simple in geometry.v:215
theorem srcycle_simple {r : List G.Dart} (hs : Srcycle G r) : Simple G r := hs.2.1

-- Coq: scycle_uniq in geometry.v:218
theorem srcycle_nodup {r : List G.Dart} (hs : Srcycle G r) : r.Nodup := hs.1

-- Coq: scycle_pos (geometry.v, ring length > 0)
theorem srcycle_pos {r : List G.Dart} (hs : Srcycle G r) : 0 < r.length := hs.2.2.1

theorem srcycle_ne_nil {r : List G.Dart} (hs : Srcycle G r) : r ≠ [] := by
  intro h; have := hs.2.2.1; rw [h] at this; simp at this

/-
Coq: simple_cface in geometry.v:244 (helper)

In a face-simple list, face-connected members are equal.
-/
theorem simple_cface_eq {p : List G.Dart} (hs : Simple G p)
    {x y : G.Dart} (hx : x ∈ p) (hy : y ∈ p) (h : cface G x y) : x = y := by
  by_contra hne
  unfold Simple at hs
  rw [List.pairwise_iff_getElem] at hs
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  rcases lt_trichotomy i j with hij | hij | hij
  · exact hs i j hi hj hij h
  · subst hij; exact hne rfl
  · exact hs j i hj hi hij (cface_sym h)

-- Coq: scycle_cface in geometry.v:244
/-- In a simple R-cycle, face-connected members are equal. -/
theorem srcycle_cface_eq {r : List G.Dart} (hs : Srcycle G r)
    {x y : G.Dart} (hx : x ∈ r) (hy : y ∈ r) (h : cface G x y) : x = y :=
  simple_cface_eq (srcycle_simple hs) hx hy h

/-! ### 21. `insertE_replicate` (geometry.v:780–782, `insertE_seqb`) -/

-- Coq: insertE_seqb in geometry.v:780
theorem insertE_replicate (b : Bool) (x : G.Dart) :
    insertE G (List.replicate b.toNat x) =
    List.replicate b.toNat x ++ List.replicate b.toNat (G.edge x) := by
  cases b <;> rfl

/-! ### 22. `fband_snoc` (geometry.v:273–276, `fband_rcons`) -/

-- Coq: fband_rcons in geometry.v:273
theorem fband_snoc (p : List G.Dart) (x y : G.Dart) :
    fband G (p ++ [x]) y ↔ cface G y x ∨ fband G p y := by
  constructor
  · rintro ⟨z, hz_mem, hz_face⟩
    rcases List.mem_append.mp hz_mem with hz_mem | hz_mem
    · exact Or.inr ⟨z, hz_mem, hz_face⟩
    · exact Or.inl (by rw [List.mem_singleton] at hz_mem; rwa [hz_mem] at hz_face)
  · rintro (h | ⟨z, hz_mem, hz_face⟩)
    · exact ⟨x, List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)), h⟩
    · exact ⟨z, List.mem_append.mpr (Or.inl hz_mem), hz_face⟩

/-! ### 23. `fband_replicate` (geometry.v:277–284, `fband_nseq`) -/

-- Coq: fband_nseq in geometry.v:277
theorem fband_replicate (n : ℕ) (x y : G.Dart) :
    fband G (List.replicate n x) y ↔ 0 < n ∧ cface G y x := by
  induction n with
  | zero => simp [fband]
  | succ n ih =>
    simp only [List.replicate_succ, fband_cons, ih, Nat.zero_lt_succ, true_and]
    constructor
    · rintro (h | ⟨_, h⟩)
      · exact h
      · exact h
    · intro h
      exact Or.inl h

/-! ### 24. `fband_singleton` -/

@[simp] theorem fband_singleton (x y : G.Dart) :
    fband G [x] y ↔ cface G y x := by
  simp [fband]

/-! ================================================================
    Batch 3: `cface` / `cnode` / `cedge` under `dual` and `mirror`.
    ================================================================ -/

/-! ### 25. Inverse-permutation orbit correspondence

Iterating `Function.invFun f` from `x` reaches `y` iff iterating `f`
from `y` reaches `x`.  The proof is purely algebraic: `f` and
`invFun f` are mutual inverses, so their iterates are as well. -/

private theorem invFun_comp_apply {α : Type*} [Nonempty α]
    {f : α → α} (hbij : Function.Bijective f) (x : α) :
    Function.invFun f (f x) = x :=
  hbij.1 (Function.rightInverse_invFun hbij.2 (f x))

private theorem iterate_apply_iterate_invFun {α : Type*} [Nonempty α]
    {f : α → α} (hbij : Function.Bijective f)
    (n : ℕ) (x : α) : f^[n] ((Function.invFun f)^[n] x) = x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply f,
        Function.iterate_succ_apply' (Function.invFun f),
        Function.rightInverse_invFun hbij.2, ih]

private theorem iterate_invFun_apply_iterate {α : Type*} [Nonempty α]
    {f : α → α} (hbij : Function.Bijective f)
    (n : ℕ) (x : α) : (Function.invFun f)^[n] (f^[n] x) = x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply (Function.invFun f),
        Function.iterate_succ_apply' f,
        invFun_comp_apply hbij, ih]

/-- Iterating an inverse permutation from `x` reaches `y` iff iterating
    the original permutation from `y` reaches `x`, in a finite setting. -/
private theorem iterate_invFun_iff {α : Type*} [Finite α] [Nonempty α]
    {f : α → α} (hbij : Function.Bijective f) (x y : α) :
    (∃ n, (Function.invFun f)^[n] x = y) ↔ (∃ n, f^[n] y = x) := by
  constructor
  · rintro ⟨n, rfl⟩; exact ⟨n, iterate_apply_iterate_invFun hbij n x⟩
  · rintro ⟨n, rfl⟩; exact ⟨n, iterate_invFun_apply_iterate hbij n y⟩

/-! ### 16b. `arity_mirror` (geometry.v:161) -/

/-- `minimalPeriod` is the same for a bijection and its inverse. -/
private theorem minimalPeriod_invFun_of_bijective {α : Type*} [Finite α] [Nonempty α]
    {f : α → α} (hbij : Function.Bijective f) (x : α) :
    Function.minimalPeriod (Function.invFun f) x = Function.minimalPeriod f x := by
  rw [Function.minimalPeriod_eq_minimalPeriod_iff]
  intro n
  simp only [Function.IsPeriodicPt, Function.IsFixedPt]
  constructor
  · intro h
    have := iterate_apply_iterate_invFun hbij n x
    rw [h] at this; exact this
  · intro h
    have := iterate_invFun_apply_iterate hbij n x
    rw [h] at this; exact this

/-- Face arity is preserved by mirroring.
    Corresponds to `arity_mirror` in geometry.v:161. -/
theorem arity_mirror (G : Hypermap) (x : G.Dart) :
    @arity (mirror G) x = arity G x := by
  simp only [arity, orderOf, mirror_face]
  exact minimalPeriod_invFun_of_bijective face_bijective x

/-! ### 26. `cface` / `cnode` / `cedge` under `mirror`

`mirror` replaces face with `invFun face` and node with `invFun node`. -/

theorem cface_mirror {x y : G.Dart} :
    cface (mirror G) x y ↔ cface G y x := by
  show (∃ n, (Function.invFun G.face)^[n] x = y) ↔ (∃ n, G.face^[n] y = x)
  exact iterate_invFun_iff face_bijective x y

theorem cnode_mirror {x y : G.Dart} :
    cnode (mirror G) x y ↔ cnode G y x := by
  show (∃ n, (Function.invFun G.node)^[n] x = y) ↔ (∃ n, G.node^[n] y = x)
  exact iterate_invFun_iff node_bijective x y

/-! ### 27. `cedge` / `cnode` / `cface` under `dual`

`dual` maps edge ↦ invFun edge, node ↦ invFun face, face ↦ invFun node. -/

theorem cedge_dual {x y : G.Dart} :
    cedge (dual G) x y ↔ cedge G y x := by
  show (∃ n, (Function.invFun G.edge)^[n] x = y) ↔ (∃ n, G.edge^[n] y = x)
  exact iterate_invFun_iff edge_bijective x y

theorem cnode_dual {x y : G.Dart} :
    cnode (dual G) x y ↔ cface G y x := by
  show (∃ n, (Function.invFun G.face)^[n] x = y) ↔ (∃ n, G.face^[n] y = x)
  exact iterate_invFun_iff face_bijective x y

theorem cface_dual {x y : G.Dart} :
    cface (dual G) x y ↔ cnode G y x := by
  show (∃ n, (Function.invFun G.node)^[n] x = y) ↔ (∃ n, G.node^[n] y = x)
  exact iterate_invFun_iff node_bijective x y

/-! ### 28. Dart cardinality under `mirror` (geometry.v) -/

/-- Mirror preserves the dart count. -/
theorem card_mirror' (G : Hypermap) :
    Fintype.card (mirror G).Dart = Fintype.card G.Dart := rfl

/-! ### 29. `bridgeless_mirror` (geometry.v:102) -/

/-- Bridgeless is preserved (equivalently detected) by mirroring.
    Corresponds to `bridgeless_mirror` in geometry.v:102. -/
theorem bridgeless_mirror (G : Hypermap) : Bridgeless (mirror G) ↔ Bridgeless G := by
  constructor
  · -- Bridgeless (mirror G) → Bridgeless G
    intro hBm x hcf
    -- Reformulate hBm via cface_mirror: ∀ z, ¬ cface G (G.face (G.node z)) z
    have hBm' : ∀ z : G.Dart, ¬ cface G (G.face (G.node z)) z := by
      intro z hz
      exact hBm z ((@cface_mirror G z (G.face (G.node z))).mpr hz)
    -- Apply at z = G.face (G.edge x); edgeK' gives G.node (G.face (G.edge x)) = x
    apply hBm' (G.face (G.edge x))
    rw [@edgeK' G x]
    -- Goal: cface G (G.face x) (G.face (G.edge x))
    exact @cface_trans G _ _ _ (cface_sym (cface_face x))
      (@cface_trans G _ _ _ hcf (cface_face (G.edge x)))
  · -- Bridgeless G → Bridgeless (mirror G)
    intro hB x hcfm
    -- By cface_mirror: cface G (G.face (G.node x)) x
    have hcf : cface G (G.face (G.node x)) x :=
      (@cface_mirror G x (G.face (G.node x))).mp hcfm
    -- cface G (G.node x) x by transitivity with cface_face
    have h1 : cface G (G.node x) x :=
      @cface_trans G _ _ _ (cface_face (G.node x)) hcf
    -- nodeK: G.face (G.edge (G.node x)) = x, giving one face step
    have h2 : cface G (G.edge (G.node x)) x :=
      ⟨1, @nodeK G x⟩
    -- Combine: cface G (G.node x) (G.edge (G.node x))
    have h3 : cface G (G.node x) (G.edge (G.node x)) :=
      @cface_trans G _ _ _ h1 (cface_sym h2)
    exact hB (G.node x) h3

/-! ### 30. `bridgeless_dual` (geometry.v:95) -/

private theorem dual_edge_eq_finvEdge (x : G.Dart) :
    (dual G).edge x = G.finvEdge x := by
  have h1 : G.edge (Function.invFun G.edge x) = x :=
    Function.rightInverse_invFun G.edge_surjective x
  have h2 : G.edge (G.finvEdge x) = x := edge_finvEdge x
  exact G.edge_injective (h1.trans h2.symm)

/-- Bridgeless on dual corresponds to Loopless on the original.
    Coq: geometry.v:95 (`bridgeless_dual`). -/
theorem bridgeless_dual (G : Hypermap) : Bridgeless (dual G) ↔ Loopless G := by
  constructor
  · -- Bridgeless (dual G) → Loopless G
    intro hBd y hcn
    apply hBd (G.edge y)
    show cface (dual G) (G.edge y) ((dual G).edge (G.edge y))
    rw [dual_edge_eq_finvEdge, finvEdge_edge]
    exact cface_dual.mpr hcn
  · -- Loopless G → Bridgeless (dual G)
    intro hL x hcfd
    apply hL (G.finvEdge x)
    rw [edge_finvEdge]
    have h := cface_dual.mp hcfd
    rw [dual_edge_eq_finvEdge] at h
    exact h

/-! ### 31. `fband_iter_face` -/

/-- The face band is closed under iterated face application.
    Corresponds to iterated `fbandF` in geometry.v. -/
theorem fband_iter_face (p : List G.Dart) (x : G.Dart) (n : ℕ) :
    fband G p (G.face^[n] x) ↔ fband G p x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rw [fband_face]
    exact ih

/-! ### 32. `kernel_iter_face` -/

/-- The kernel is closed under iterated face application. -/
theorem kernel_iter_face (p : List G.Dart) (x : G.Dart) (n : ℕ) :
    kernel G p (G.face^[n] x) ↔ kernel G p x := by
  simp only [kernel, fband_iter_face]

/-! ### 33. `loopless_sym` -/

/-- Loopless is equivalent to: no edge-link inside a single node orbit,
    stated with endpoints reversed. -/
theorem loopless_sym (G : Hypermap) : Loopless G ↔ ∀ x, ¬ cnode G (G.edge x) x := by
  unfold Loopless
  exact ⟨fun h x hne => h x (cnode_sym hne), fun h x hne => h x (cnode_sym hne)⟩

/-! ### 34. `bridgeless` corollaries -/

/-- In a bridgeless hypermap, a dart's edge image is never face-connected
    back to the dart (restated with endpoints reversed). -/
theorem bridgeless_not_cedge_face (hB : Bridgeless G) (x : G.Dart) :
    ¬ cface G (G.edge x) x := fun h => hB x (cface_sym h)

/-- Bridgeless implies no face-connection between an iterated-face image
    and the edge image. -/
theorem bridgeless_not_cface_iter (hB : Bridgeless G) (x : G.Dart) (n : ℕ) :
    ¬ cface G (G.face^[n] x) (G.edge x) := fun h =>
  hB x (cface_trans (cface_iter_face n x) h)

/-! ### 35. `adj` / `fband` interaction

`adj_sym` requires the dual `adjN` infrastructure that hasn't been ported yet;
left for a follow-up batch. -/

/-- If `y` is adjacent to some dart in the face band of `p`, then `y`
    is adjacent to some member of `p` directly. -/
theorem adj_fband {p : List G.Dart} {x y : G.Dart}
    (hadj : adj G x y) (hfb : fband G p y) :
    ∃ z ∈ p, adj G x z := by
  obtain ⟨w, hxw, hyw⟩ := hadj
  obtain ⟨u, hu_mem, hu_face⟩ := hfb
  exact ⟨u, hu_mem, w, hxw, cface_trans (cface_sym hu_face) hyw⟩

/-! ### 36. `cface` / `cedge` / `cnode` iteration helpers -/

/-- Given `cface G x y`, produce the iteration count. -/
theorem cface.exists_iterate {x y : G.Dart}
    (h : cface G x y) : ∃ n, G.face^[n] x = y := h

/-- Given `cedge G x y`, produce the iteration count. -/
theorem cedge.exists_iterate {x y : G.Dart}
    (h : cedge G x y) : ∃ n, G.edge^[n] x = y := h

/-- Given `cnode G x y`, produce the iteration count. -/
theorem cnode.exists_iterate {x y : G.Dart}
    (h : cnode G x y) : ∃ n, G.node^[n] x = y := h

/-- If `cface G x y`, any face iterate of `y` is also in the cface orbit. -/
theorem cface_iter_face_right {x y : G.Dart}
    (h : cface G x y) (n : ℕ) : cface G x (G.face^[n] y) := by
  obtain ⟨m, rfl⟩ := h
  exact ⟨n + m, by rw [Function.iterate_add_apply]⟩

/-- If `cedge G x y`, any edge iterate of `y` is also in the cedge orbit. -/
theorem cedge_iter_edge_right {x y : G.Dart}
    (h : cedge G x y) (n : ℕ) : cedge G x (G.edge^[n] y) := by
  obtain ⟨m, rfl⟩ := h
  exact ⟨n + m, by rw [Function.iterate_add_apply]⟩

/-- If `cnode G x y`, any node iterate of `y` is also in the cnode orbit. -/
theorem cnode_iter_node_right {x y : G.Dart}
    (h : cnode G x y) (n : ℕ) : cnode G x (G.node^[n] y) := by
  obtain ⟨m, rfl⟩ := h
  exact ⟨n + m, by rw [Function.iterate_add_apply]⟩

/-- Prepending face iterates on the left preserves `cface`. -/
theorem cface_iter_face_left (x : G.Dart) (n : ℕ) {y : G.Dart}
    (h : cface G (G.face^[n] x) y) : cface G x y := by
  obtain ⟨m, rfl⟩ := h
  exact ⟨m + n, by rw [← Function.iterate_add_apply, Nat.add_comm]⟩

/-- Prepending edge iterates on the left preserves `cedge`. -/
theorem cedge_iter_edge_left (x : G.Dart) (n : ℕ) {y : G.Dart}
    (h : cedge G (G.edge^[n] x) y) : cedge G x y := by
  obtain ⟨m, rfl⟩ := h
  exact ⟨m + n, by rw [← Function.iterate_add_apply, Nat.add_comm]⟩

/-- Prepending node iterates on the left preserves `cnode`. -/
theorem cnode_iter_node_left (x : G.Dart) (n : ℕ) {y : G.Dart}
    (h : cnode G (G.node^[n] x) y) : cnode G x y := by
  obtain ⟨m, rfl⟩ := h
  exact ⟨m + n, by rw [← Function.iterate_add_apply, Nat.add_comm]⟩

/-- Two face iterates from the same dart are in the same face orbit. -/
theorem cface_iter_iter_face (n m : ℕ) (x : G.Dart) :
    cface G (G.face^[n] x) (G.face^[m] x) :=
  cface_trans (cface_sym (cface_iter_face n x)) (cface_iter_face m x)

/-- Two edge iterates from the same dart are in the same edge orbit. -/
theorem cedge_iter_iter_edge (n m : ℕ) (x : G.Dart) :
    cedge G (G.edge^[n] x) (G.edge^[m] x) :=
  cedge_trans (cedge_sym (cedge_iter_edge n x)) (cedge_iter_edge m x)

/-- Two node iterates from the same dart are in the same node orbit. -/
theorem cnode_iter_iter_node (n m : ℕ) (x : G.Dart) :
    cnode G (G.node^[n] x) (G.node^[m] x) :=
  cnode_trans (cnode_sym (cnode_iter_node n x)) (cnode_iter_node m x)

/-! ## Convenience lemmas: fband, Simple, kernel -/

/-- The face band is invariant under list reversal. -/
theorem fband_reverse (p : List G.Dart) (x : G.Dart) :
    fband G p.reverse x ↔ fband G p x := by
  simp only [fband, List.mem_reverse]

/-- A singleton list is always face-simple. -/
theorem Simple.singleton (x : G.Dart) : Simple G [x] :=
  List.pairwise_singleton _ _

/-- Face-simplicity is preserved under list reversal. -/
theorem Simple.reverse {p : List G.Dart} (h : Simple G p) :
    Simple G p.reverse := by
  unfold Simple at h ⊢
  rw [List.pairwise_reverse]
  exact h.imp fun hab => hab ∘ cface_sym

/-- The kernel of an empty list is the full set. -/
@[simp] theorem kernel_nil (x : G.Dart) : kernel G [] x := by
  intro ⟨_, hm, _⟩
  exact List.not_mem_nil hm

@[simp] theorem kernel_cons (y : G.Dart) (p : List G.Dart) (x : G.Dart) :
    kernel G (y :: p) x ↔ ¬ cface G x y ∧ kernel G p x := by
  unfold kernel
  rw [fband_cons]
  push_neg
  rfl

@[simp] theorem kernel_singleton (x y : G.Dart) :
    kernel G [x] y ↔ ¬ cface G y x := by
  unfold kernel
  rw [fband_singleton]

@[simp] theorem fproj_nil (x : G.Dart) : fproj G [] x = x := by
  unfold fproj
  split
  case isTrue h =>
    exact absurd h (by rintro ⟨_, hm, _⟩; exact List.not_mem_nil hm)
  case isFalse => rfl

/-! ## nComp_dual and nComp_mirror -/

/-- A single glink step in `dual G` generates an EqvGen step in `G`. -/
private theorem glink_dual_eqvGen (x y : G.Dart) (h : glink (dual G) x y) :
    Relation.EqvGen (glink G) x y := by
  rcases h with rfl | rfl | rfl
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
      (Or.inl (Function.rightInverse_invFun edge_surjective x)))
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
      (Or.inr (Or.inr (Function.rightInverse_invFun face_surjective x))))
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
      (Or.inr (Or.inl (Function.rightInverse_invFun node_surjective x))))

/-- A single glink step in `G` generates an EqvGen step in `dual G`. -/
private theorem glink_eqvGen_dual (x y : G.Dart) (h : glink G x y) :
    Relation.EqvGen (glink (dual G)) x y := by
  rcases h with rfl | rfl | rfl
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
      (Or.inl (Function.leftInverse_invFun edge_bijective.injective x)))
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
      (Or.inr (Or.inr (Function.leftInverse_invFun node_bijective.injective x))))
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
      (Or.inr (Or.inl (Function.leftInverse_invFun face_bijective.injective x))))

/-- The EqvGen closures of glink for `G` and `dual G` coincide. -/
private theorem eqvGen_glink_dual_iff (x y : G.Dart) :
    Relation.EqvGen (glink (dual G)) x y ↔ Relation.EqvGen (glink G) x y := by
  constructor
  · intro h
    induction h with
    | rel x y h => exact glink_dual_eqvGen x y h
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  · intro h
    induction h with
    | rel x y h => exact glink_eqvGen_dual x y h
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The number of connected components is preserved by the dual construction. -/
theorem nComp_dual (G : Hypermap) : nComp (dual G) = nComp G := by
  classical
  show Fintype.card (Quotient (glinkSetoid (dual G))) =
       Fintype.card (Quotient (glinkSetoid G))
  apply Fintype.card_congr
  refine Quotient.congr (Equiv.refl G.Dart) ?_
  intro x y
  exact @eqvGen_glink_dual_iff G x y

/-- A single glink step in `mirror G` generates an EqvGen step in `G`. -/
private theorem glink_mirror_eqvGen (x y : G.Dart) (h : glink (mirror G) x y) :
    Relation.EqvGen (glink G) x y := by
  rcases h with rfl | rfl | rfl
  · exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.rel _ _ (Or.inr (Or.inl rfl)))
      (Relation.EqvGen.rel _ _ (Or.inr (Or.inr rfl)))
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
      (Or.inr (Or.inl (Function.rightInverse_invFun node_surjective x))))
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
      (Or.inr (Or.inr (Function.rightInverse_invFun face_surjective x))))

/-- A single glink step in `G` generates an EqvGen step in `mirror G`. -/
private theorem glink_eqvGen_mirror (x y : G.Dart) (h : glink G x y) :
    Relation.EqvGen (glink (mirror G)) x y := by
  rcases h with rfl | rfl | rfl
  · have h1 : (mirror G).face ((mirror G).node x) = G.edge x := by
      show Function.invFun G.face (Function.invFun G.node x) = G.edge x
      have : G.node (G.face (G.edge x)) = x := G.edgeK x
      have hfex : G.face (G.edge x) = Function.invFun G.node x := by
        have := Function.rightInverse_invFun node_surjective x
        exact node_injective (this.symm ▸ ‹G.node (G.face (G.edge x)) = x›)
      rw [← hfex, Function.leftInverse_invFun face_bijective.injective]
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.rel _ _ (Or.inr (Or.inl rfl)))
      (Relation.EqvGen.rel _ _ (Or.inr (Or.inr h1)))
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
      (Or.inr (Or.inl (Function.leftInverse_invFun node_bijective.injective x))))
  · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
      (Or.inr (Or.inr (Function.leftInverse_invFun face_bijective.injective x))))

/-- The EqvGen closures of glink for `G` and `mirror G` coincide. -/
private theorem eqvGen_glink_mirror_iff (x y : G.Dart) :
    Relation.EqvGen (glink (mirror G)) x y ↔ Relation.EqvGen (glink G) x y := by
  constructor
  · intro h
    induction h with
    | rel x y h => exact glink_mirror_eqvGen x y h
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  · intro h
    induction h with
    | rel x y h => exact glink_eqvGen_mirror x y h
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

/-- The number of connected components is preserved by the mirror construction. -/
theorem nComp_mirror (G : Hypermap) : nComp (mirror G) = nComp G := by
  classical
  show Fintype.card (Quotient (glinkSetoid (mirror G))) =
       Fintype.card (Quotient (glinkSetoid G))
  apply Fintype.card_congr
  refine Quotient.congr (Equiv.refl G.Dart) ?_
  intro x y
  exact @eqvGen_glink_mirror_iff G x y

/-! ## Cubic / Plain / Quasicubic / Pentagonal projections -/

theorem Cubic.precubic {G : Hypermap} (h : Cubic G) : Precubic G :=
  fun x => (h x).1

theorem Cubic.node_ne {G : Hypermap} (h : Cubic G) (x : G.Dart) : G.node x ≠ x :=
  (h x).2.1

theorem Cubic.node_node_ne {G : Hypermap} (h : Cubic G) (x : G.Dart) :
    G.node (G.node x) ≠ x := (h x).2.2

theorem Plain.edge_inv {G : Hypermap} (h : Plain G) (x : G.Dart) :
    G.edge (G.edge x) = x := (h x).1

theorem Plain.edge_ne {G : Hypermap} (h : Plain G) (x : G.Dart) : G.edge x ≠ x :=
  (h x).2

/-- Full cubic triple for a dart outside the ring of a quasicubic map. -/
theorem Quasicubic.cubic_off_ring {G : Hypermap} {r : Finset G.Dart}
    (h : Quasicubic G r) {x : G.Dart} (hx : x ∉ r) :
    G.node (G.node (G.node x)) = x ∧ G.node x ≠ x ∧ G.node (G.node x) ≠ x := h x hx

theorem Quasicubic.precubic_off_ring {G : Hypermap} {r : Finset G.Dart}
    (h : Quasicubic G r) {x : G.Dart} (hx : x ∉ r) :
    G.node (G.node (G.node x)) = x := (h x hx).1

theorem Pentagonal.arity_ge_five {G : Hypermap} (h : Pentagonal G) (x : G.Dart) :
    5 ≤ arity G x := h x

theorem Plain.edge_injective_on_support {G : Hypermap} (_hP : Plain G)
    (s : Finset G.Dart) : Set.InjOn G.edge ↑s :=
  fun _ _ _ _ h => G.edge_injective h

/-! ## rlink / Srcycle shape helpers -/

theorem rlink_def (G : Hypermap) (x y : G.Dart) :
    rlink G x y ↔ cface G (G.node x) y := Iff.rfl

theorem rlink_face_node (G : Hypermap) (x : G.Dart) : rlink G x (G.node x) :=
  cface_refl _

theorem Srcycle.ne_nil {G : Hypermap} {r : List G.Dart} (h : Srcycle G r) :
    r ≠ [] := srcycle_ne_nil h

theorem Srcycle.length_pos {G : Hypermap} {r : List G.Dart} (h : Srcycle G r) :
    0 < r.length := srcycle_pos h

theorem Srcycle.nodup {G : Hypermap} {r : List G.Dart} (h : Srcycle G r) :
    r.Nodup := srcycle_nodup h

theorem Srcycle.simple {G : Hypermap} {r : List G.Dart} (h : Srcycle G r) :
    Simple G r := srcycle_simple h

/-- An Srcycle is a Simple list (alias). -/
theorem Srcycle.toSimple {G : Hypermap} {r : List G.Dart} (h : Srcycle G r) :
    Simple G r := h.simple

/-- An Srcycle is Nodup (alias). -/
theorem Srcycle.toNodup {G : Hypermap} {r : List G.Dart} (h : Srcycle G r) :
    r.Nodup := h.nodup

/-! ## cface / cedge / cnode constructor helpers -/

theorem cface_zero (G : Hypermap) (x : G.Dart) : cface G x x := ⟨0, rfl⟩

theorem cface_of_iterate (G : Hypermap) (n : ℕ) (x : G.Dart) :
    cface G x (G.face^[n] x) := ⟨n, rfl⟩

theorem cedge_of_iterate (G : Hypermap) (n : ℕ) (x : G.Dart) :
    cedge G x (G.edge^[n] x) := ⟨n, rfl⟩

theorem cnode_of_iterate (G : Hypermap) (n : ℕ) (x : G.Dart) :
    cnode G x (G.node^[n] x) := ⟨n, rfl⟩

theorem cface_one (G : Hypermap) (x : G.Dart) : cface G x (G.face x) := ⟨1, rfl⟩

theorem cface_step_right {G : Hypermap} {x y : G.Dart} (h : cface G x y) :
    cface G x (G.face y) := by
  obtain ⟨n, rfl⟩ := h
  exact ⟨n + 1, by rw [Function.iterate_succ_apply']⟩

theorem cedge_step_right {G : Hypermap} {x y : G.Dart} (h : cedge G x y) :
    cedge G x (G.edge y) := by
  obtain ⟨n, rfl⟩ := h
  exact ⟨n + 1, by rw [Function.iterate_succ_apply']⟩

theorem cnode_step_right {G : Hypermap} {x y : G.Dart} (h : cnode G x y) :
    cnode G x (G.node y) := by
  obtain ⟨n, rfl⟩ := h
  exact ⟨n + 1, by rw [Function.iterate_succ_apply']⟩

/-! ## cedge_plain corollaries -/

theorem cedge_plain_sym (hP : Plain G) {x y : G.Dart} (h : cedge G x y) :
    cedge G y x := by
  rcases (cedge_plain hP x y).mp h with rfl | rfl
  · exact cedge_refl x
  · exact ⟨1, plain_edge_invol hP x⟩

theorem cedge_plain_card (hP : Plain G) (x : G.Dart) :
    ∀ y, cedge G x y → y = x ∨ y = G.edge x := by
  intro y h
  rcases (cedge_plain hP x y).mp h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem edge_iter_two_plain (hP : Plain G) (x : G.Dart) :
    G.edge^[2] x = x := by
  show G.edge (G.edge x) = x
  exact plain_edge_invol hP x

/-! ## arity unfolding helpers -/

theorem arity_def (x : G.Dart) :
    arity G x = Function.minimalPeriod G.face x := rfl

theorem arity_eq_of_cface {x y : G.Dart} (h : cface G x y) :
    arity G x = arity G y := arity_cface h

theorem arity_eq_of_cface_symm {x y : G.Dart} (h : cface G x y) :
    arity G y = arity G x := (arity_cface h).symm

theorem arity_pos (x : G.Dart) : 0 < arity G x := by
  unfold arity orderOf
  exact Function.minimalPeriod_pos_of_mem_periodicPts
    (Function.Injective.mem_periodicPts face_injective x)

theorem arity_face_iter (G : Hypermap) (n : ℕ) (x : G.Dart) :
    arity G (G.face^[n] x) = arity G x := arity_iter_face n x

@[simp] theorem arity_eq_zero_iff (G : Hypermap) (x : G.Dart) :
    arity G x = 0 ↔ False := by
  constructor
  · intro h
    have := arity_pos x
    omega
  · intro h
    exact h.elim

/-- arity is constant along a cface orbit (alias of `arity_eq_of_cface`). -/
theorem arity_const_of_cface (G : Hypermap) {x y : G.Dart}
    (h : cface G x y) : arity G x = arity G y :=
  arity_eq_of_cface h

/-- The arity is at least 1. -/
theorem one_le_arity (G : Hypermap) (x : G.Dart) : 1 ≤ arity G x := arity_pos x

/-! ## cnode/cedge zero & one helpers (counterparts to cface_zero/one) -/

theorem cedge_zero (x : G.Dart) : cedge G x x := ⟨0, rfl⟩
theorem cnode_zero (x : G.Dart) : cnode G x x := ⟨0, rfl⟩
theorem cedge_one (x : G.Dart) : cedge G x (G.edge x) := ⟨1, rfl⟩
theorem cnode_one (x : G.Dart) : cnode G x (G.node x) := ⟨1, rfl⟩

/-! ## Step / iter aliases for cface / cedge / cnode -/

theorem cface_step (G : Hypermap) (x : G.Dart) : cface G x (G.face x) := ⟨1, rfl⟩
theorem cedge_step (G : Hypermap) (x : G.Dart) : cedge G x (G.edge x) := ⟨1, rfl⟩
theorem cnode_step (G : Hypermap) (x : G.Dart) : cnode G x (G.node x) := ⟨1, rfl⟩

theorem cface_face_sym (G : Hypermap) (x : G.Dart) : cface G (G.face x) x :=
  cface_sym (cface_step G x)

theorem cface_iter (G : Hypermap) (x : G.Dart) (n : ℕ) : cface G x (G.face^[n] x) := ⟨n, rfl⟩
theorem cedge_iter (G : Hypermap) (x : G.Dart) (n : ℕ) : cedge G x (G.edge^[n] x) := ⟨n, rfl⟩
theorem cnode_iter (G : Hypermap) (x : G.Dart) (n : ℕ) : cnode G x (G.node^[n] x) := ⟨n, rfl⟩

/-- In a plain hypermap, `node ∘ face = edge` (from `faceK` and edge involution). -/
theorem cnode_plain (hP : Plain G) (x : G.Dart) : G.node (G.face x) = G.edge x :=
  edge_injective (by rw [faceK, plain_edge_invol hP])

/-! ## Bridgeless / Loopless projection helpers -/

theorem Bridgeless.iff_forall (G : Hypermap) :
    Bridgeless G ↔ ∀ x, ¬ cface G x (G.edge x) := Iff.rfl

theorem Bridgeless.intro {G : Hypermap}
    (h : ∀ x, ¬ cface G x (G.edge x)) : Bridgeless G := h

theorem Loopless.iff_forall (G : Hypermap) :
    Loopless G ↔ ∀ x, ¬ cnode G x (G.edge x) := Iff.rfl

theorem Loopless.intro {G : Hypermap}
    (h : ∀ x, ¬ cnode G x (G.edge x)) : Loopless G := h

theorem Bridgeless.at {G : Hypermap} (h : Bridgeless G) (x : G.Dart) :
    ¬ cface G x (G.edge x) := h x

theorem Loopless.at {G : Hypermap} (h : Loopless G) (x : G.Dart) :
    ¬ cnode G x (G.edge x) := h x

/-! ## kernel / fband interaction helpers -/

theorem kernel_not_fband (p : List G.Dart) (x : G.Dart) :
    kernel G p x ↔ ¬ fband G p x := Iff.rfl

theorem mem_kernel_iff_not_fband (p : List G.Dart) (x : G.Dart) :
    kernel G p x ↔ ¬ fband G p x := Iff.rfl

theorem fband_subset_iff (p q : List G.Dart) :
    (∀ x, fband G p x → fband G q x) ↔ ∀ y ∈ p, ∃ z ∈ q, cface G y z := by
  constructor
  · intro hsub y hy
    have := hsub y ⟨y, hy, cface_refl y⟩
    obtain ⟨z, hz_mem, hz_face⟩ := this
    exact ⟨z, hz_mem, hz_face⟩
  · intro hsub x ⟨y, hy_mem, hy_face⟩
    obtain ⟨z, hz_mem, hyz⟩ := hsub y hy_mem
    exact ⟨z, hz_mem, cface_trans hy_face hyz⟩

theorem kernel_append (G : Hypermap) (p q : List G.Dart) (x : G.Dart) :
    kernel G (p ++ q) x ↔ kernel G p x ∧ kernel G q x := by
  unfold kernel
  rw [fband_append]
  exact not_or

/-- The kernel decomposes over append (negation form of fband_append). -/
theorem kernel_append_iff (G : Hypermap) (p q : List G.Dart) (x : G.Dart) :
    kernel G (p ++ q) x ↔ kernel G p x ∧ kernel G q x :=
  kernel_append G p q x

/-- Membership in fband is symmetric in band-orbit (cface-orbit). -/
theorem fband_iff_exists_mem (G : Hypermap) (p : List G.Dart) (x : G.Dart) :
    fband G p x ↔ ∃ y ∈ p, cface G x y := Iff.rfl

end Hypermap