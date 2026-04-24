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

-- Coq: simple_cat / simple_catC in geometry.v
theorem simple_append (p q : List G.Dart) :
    Simple G (p ++ q) ↔ Simple G p ∧ Simple G q ∧
      (∀ x ∈ p, ∀ y ∈ q, ¬ cface G x y) := by
  exact List.pairwise_append

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

/-! ### 15. `bridgeless_mirror` (geometry.v:102) -/
-- TODO: Relating cface in G and cface in mirror G requires substantial
-- infrastructure (inverse-permutation orbit correspondence). Skipped for now.

/-! ### 16. `arity_mirror` (geometry.v:161) -/
-- TODO: Requires `Function.minimalPeriod` lemma for inverse permutations.
-- Skipped for now.

end Hypermap
