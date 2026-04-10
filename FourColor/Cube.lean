/-
Copyright (c) 2006-2018 Microsoft Corporation and Inria (Coq version).
Lean 4 port of the Four Color Theorem formalization.

Reduction of the coloring problem to cubic maps. The cube construction
transforms any hypermap into a plain cubic one that is four-colorable
only if the original is, and preserves planarity and bridgelessness.

Each dart in G splits into six darts in cube G; there is a face in
cube G for each face, node, and edge in G.
-/
import FourColor.Hypermap
import FourColor.Geometry
import FourColor.Coloring

set_option maxHeartbeats 400000

open Hypermap

namespace Hypermap

/-! ## Cube tag -/

/-- The six tags for the cube construction. -/
inductive CubeTag : Type where
  | CTn : CubeTag    -- node copy
  | CTen : CubeTag   -- edge-node copy
  | CTf : CubeTag    -- face copy
  | CTnf : CubeTag   -- node-face copy
  | CTe : CubeTag    -- edge copy
  | CTfe : CubeTag   -- face-edge copy
  deriving DecidableEq, Repr

instance : Fintype CubeTag where
  elems := {CubeTag.CTn, CubeTag.CTen, CubeTag.CTf,
            CubeTag.CTnf, CubeTag.CTe, CubeTag.CTfe}
  complete := by intro x; cases x <;> simp

instance : Nonempty CubeTag := ⟨CubeTag.CTn⟩
instance : Inhabited CubeTag := ⟨CubeTag.CTn⟩

/-! ## Cube construction -/

/-- The cube_edge permutation (from Coq's cube_edge). -/
def cubeEdge (G : Hypermap) : CubeTag × G.Dart → CubeTag × G.Dart
  | (CubeTag.CTn,  x) => (CubeTag.CTfe, x)
  | (CubeTag.CTen, x) => (CubeTag.CTnf, G.edge x)
  | (CubeTag.CTf,  x) => (CubeTag.CTe,  G.node (G.face x))
  | (CubeTag.CTnf, x) => (CubeTag.CTen, G.node (G.face x))
  | (CubeTag.CTe,  x) => (CubeTag.CTf,  G.edge x)
  | (CubeTag.CTfe, x) => (CubeTag.CTn,  x)

/-- The cube_node permutation (from Coq's cube_node). -/
def cubeNode (G : Hypermap) : CubeTag × G.Dart → CubeTag × G.Dart
  | (CubeTag.CTn,  x) => (CubeTag.CTen, G.node x)
  | (CubeTag.CTen, x) => (CubeTag.CTfe, x)
  | (CubeTag.CTf,  x) => (CubeTag.CTnf, G.edge x)
  | (CubeTag.CTnf, x) => (CubeTag.CTe,  G.node (G.face x))
  | (CubeTag.CTe,  x) => (CubeTag.CTf,  x)
  | (CubeTag.CTfe, x) => (CubeTag.CTn,  G.face (G.edge x))

/-- The cube_face permutation (from Coq's cube_face). -/
def cubeFace (G : Hypermap) : CubeTag × G.Dart → CubeTag × G.Dart
  | (CubeTag.CTn,  x) => (CubeTag.CTen, x)
  | (CubeTag.CTen, x) => (CubeTag.CTf,  x)
  | (CubeTag.CTf,  x) => (CubeTag.CTnf, x)
  | (CubeTag.CTnf, x) => (CubeTag.CTn,  G.face x)
  | (CubeTag.CTe,  x) => (CubeTag.CTe,  G.edge x)
  | (CubeTag.CTfe, x) => (CubeTag.CTfe, G.node x)

/-- The triangular identity for the cube. -/
theorem cube_cancel3 (G : Hypermap) (u : CubeTag × G.Dart) :
    cubeNode G (cubeFace G (cubeEdge G u)) = u := by
  obtain ⟨o, x⟩ := u
  cases o <;> simp [cubeEdge, cubeNode, cubeFace, faceK, nodeK]

/-- The cube of a hypermap: a plain cubic hypermap obtained by replacing
    each dart with six copies. -/
noncomputable def cube (G : Hypermap) : Hypermap where
  Dart := CubeTag × G.Dart
  instNonempty := inferInstance
  edge := cubeEdge G
  node := cubeNode G
  face := cubeFace G
  edgeK := cube_cancel3 G

/-! ## Properties of the cube construction -/

/-
The cube is always plain (edges have order 2).
-/
theorem plain_cube (G : Hypermap) : Plain (cube G) := by
  rintro ⟨ o, x ⟩;
  cases o <;> simp +decide [ Hypermap.cube ];
  all_goals repeat erw [ cubeEdge ];
  all_goals simp +decide [ Hypermap.faceK ]

/-
The cube is always cubic (nodes have order 3).
-/
theorem cubic_cube (G : Hypermap) : Cubic (cube G) := by
  rintro ⟨ tag, x ⟩;
  cases tag <;> simp +decide [ *, Hypermap.cube ];
  all_goals unfold Hypermap.cubeNode; simp +decide [ Hypermap.nodeK, Hypermap.faceK ] ;

/-- Planarity is preserved by the cube construction. -/
theorem planar_cube (G : Hypermap) : Planar G ↔ Planar (cube G) := by
  sorry

/-
cface is symmetric on finite hypermaps: if face^n(x) = y, then face^m(y) = x for some m.
-/
theorem cface_sym {G : Hypermap} (x y : G.Dart) : cface G x y → cface G y x := by
  intro h
  obtain ⟨n, hn⟩ := h
  have h_inv : ∃ m, (G.face^[m] y) = x := by
    -- Since $G$ is a finite hypermap, $G.face$ is injective and surjective (by Finite.injective_iff_surjective). So $G.face$ has finite order: there exists $p > 0$ with $G.face^p = id$.
    obtain ⟨p, hp⟩ : ∃ p : ℕ, 0 < p ∧ G.face^[p] = id := by
      use (Fintype.card (Equiv.Perm G.Dart));
      refine' ⟨ Fintype.card_pos, _ ⟩;
      have h_order : ∀ f : Equiv.Perm G.Dart, f ^ Fintype.card (Equiv.Perm G.Dart) = 1 := by
        exact fun f => by rw [ pow_card_eq_one ] ;
      convert congr_arg ( fun f : Equiv.Perm G.Dart => f.toFun ) ( h_order ( Equiv.ofBijective G.face face_bijective ) ) using 1;
    use p - n % p;
    rw [ ← hn, ← Function.iterate_add_apply ];
    rw [ show p - n % p + n = p * ( n / p + 1 ) by linarith [ Nat.div_add_mod n p, Nat.sub_add_cancel ( show n % p ≤ p from Nat.le_of_lt ( Nat.mod_lt _ hp.1 ) ) ] ];
    simp +decide [ *, Function.iterate_mul, Function.iterate_fixed ]
  exact h_inv

/-
Face iteration in the cube preserves tag structure: iterating cubeFace
    on a (CTn/CTen/CTf/CTnf, x) always yields a tag in {CTn, CTen, CTf, CTnf},
    and the second component is determined by the face orbit in G.
-/
private theorem cubeFace_tag_mixed (G : Hypermap) (x : G.Dart) (n : ℕ) :
    (∃ y, (cubeFace G)^[n] (CubeTag.CTn, x) = (CubeTag.CTn, y) ∨
           (cubeFace G)^[n] (CubeTag.CTn, x) = (CubeTag.CTen, y) ∨
           (cubeFace G)^[n] (CubeTag.CTn, x) = (CubeTag.CTf, y) ∨
           (cubeFace G)^[n] (CubeTag.CTn, x) = (CubeTag.CTnf, y)) := by
  induction' n with n ih;
  · exact ⟨ x, Or.inl rfl ⟩;
  · rcases ih with ⟨ y, hy ⟩ ; simp_all +decide [ Function.iterate_succ_apply' ];
    rcases hy with ( h | h | h | h ) <;> simp_all +decide [ Hypermap.cubeFace ]

/-
Face iteration on CTe stays in CTe.
-/
private theorem cubeFace_tag_edge (G : Hypermap) (x : G.Dart) (n : ℕ) :
    ∃ y, (cubeFace G)^[n] (CubeTag.CTe, x) = (CubeTag.CTe, y) := by
  induction' n with n ih;
  · exact ⟨ x, rfl ⟩;
  · rcases ih with ⟨ y, hy ⟩ ; rw [ Function.iterate_succ_apply', hy ] ;
    exact ⟨ _, rfl ⟩

/-
Face iteration on CTfe stays in CTfe.
-/
private theorem cubeFace_tag_fe (G : Hypermap) (x : G.Dart) (n : ℕ) :
    ∃ y, (cubeFace G)^[n] (CubeTag.CTfe, x) = (CubeTag.CTfe, y) := by
  induction n <;> simp_all +decide [ Function.iterate_succ_apply' ];
  obtain ⟨ y, hy ⟩ := ‹_›; use G.node y; aesop;

/-
Face iteration from (CTen, x) follows a 4-periodic pattern.
-/
private theorem cubeFace_iter_CTen (G : Hypermap) (x : G.Dart) (k : ℕ) :
    (cubeFace G)^[4 * k] (CubeTag.CTen, x) = (CubeTag.CTen, G.face^[k] x) ∧
    (cubeFace G)^[4 * k + 1] (CubeTag.CTen, x) = (CubeTag.CTf, G.face^[k] x) ∧
    (cubeFace G)^[4 * k + 2] (CubeTag.CTen, x) = (CubeTag.CTnf, G.face^[k] x) ∧
    (cubeFace G)^[4 * k + 3] (CubeTag.CTen, x) = (CubeTag.CTn, G.face^[k + 1] x) := by
  induction' k with k ih <;> simp_all +decide [ Nat.mul_succ, Function.iterate_succ_apply' ];
  · aesop;
  · unfold Hypermap.cubeFace; aesop;

/-
Face orbit of (CTen, x) only contains darts with tags in {CTn, CTen, CTf, CTnf}
    and second component in the face orbit of x.
-/
private theorem cubeFace_CTen_cface (G : Hypermap) (x : G.Dart) (n : ℕ) :
    ∃ (t : CubeTag) (y : G.Dart),
      t ∈ ({CubeTag.CTn, CubeTag.CTen, CubeTag.CTf, CubeTag.CTnf} : Set CubeTag) ∧
      (cubeFace G)^[n] (CubeTag.CTen, x) = (t, y) ∧
      cface G x y := by
  rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> simp +decide [ *, Function.iterate_succ_apply', Nat.even_add_one ] at *;
  · rcases Nat.even_or_odd' k with ⟨ k, rfl | rfl ⟩ <;> simp +decide [ *, Function.iterate_mul, Function.iterate_fixed ] at *;
    · refine Or.inr <| Or.inl ⟨ G.face^[k] x, ?_, ?_ ⟩;
      · refine' Nat.recOn k _ _ <;> simp_all +decide [ Function.iterate_succ_apply' ];
        exact?;
      · exact ⟨ k, rfl ⟩;
    · refine' Or.inr <| Or.inr <| Or.inr ⟨ _, _, _ ⟩;
      exact G.face^[k] x;
      · induction k <;> simp_all +decide [ Function.iterate_succ_apply' ];
        · exact?;
        · unfold Hypermap.cubeFace; aesop;
      · exact ⟨ k, rfl ⟩;
  · induction k <;> simp_all +decide [ Nat.mul_succ, Function.iterate_succ_apply' ] ;
    · exact Or.inr <| Or.inr <| Or.inl ⟨ x, rfl, ⟨ 0, rfl ⟩ ⟩;
    · rename_i k hk; rcases hk with ( ⟨ y, hy, hy' ⟩ | ⟨ y, hy, hy' ⟩ | ⟨ y, hy, hy' ⟩ | ⟨ y, hy, hy' ⟩ ) <;> simp_all +decide [ Function.iterate_succ_apply', Nat.mul_succ ] ;
      · unfold Hypermap.cubeFace; simp +decide [ *, Function.iterate_succ_apply' ] ;
      · unfold Hypermap.cubeFace; simp +decide [ *, Function.iterate_succ_apply' ] ;
      · unfold Hypermap.cubeFace; simp +decide [ *, Function.iterate_succ_apply' ] ;
        exact ⟨ hy'.choose + 1, by simpa [ Function.iterate_succ_apply' ] using congr_arg G.face hy'.choose_spec ⟩;
      · unfold Hypermap.cubeFace; simp +decide [ *, Function.iterate_succ_apply' ] ;
        exact ⟨ hy'.choose + 1, by simp +decide [ Function.iterate_succ_apply', hy'.choose_spec ] ⟩

/-
Face orbit of (CTnf, x): stays in mixed tags and second component in face orbit of x.
-/
private theorem cubeFace_CTnf_mixed (G : Hypermap) (x : G.Dart) (n : ℕ) :
    ∃ (t : CubeTag) (y : G.Dart),
      (t = CubeTag.CTn ∨ t = CubeTag.CTen ∨ t = CubeTag.CTf ∨ t = CubeTag.CTnf) ∧
      (cubeFace G)^[n] (CubeTag.CTnf, x) = (t, y) := by
  simp;
  induction' n with n ih;
  · exact Or.inr <| Or.inr <| Or.inr <| ⟨ x, rfl ⟩;
  · rcases ih with ( ⟨ y, hy ⟩ | ⟨ y, hy ⟩ | ⟨ y, hy ⟩ | ⟨ y, hy ⟩ ) <;> simp_all +decide [ Function.iterate_succ_apply' ];
    · exact Or.inr <| Or.inl ⟨ _, rfl ⟩;
    · exact Or.inr <| Or.inr <| Or.inl ⟨ _, rfl ⟩;
    · exact Or.inr <| Or.inr <| Or.inr <| ⟨ _, rfl ⟩;
    · exact Or.inl ⟨ _, rfl ⟩

/-
Face orbit of (CTf, x): stays in mixed tags.
-/
private theorem cubeFace_CTf_mixed (G : Hypermap) (x : G.Dart) (n : ℕ) :
    ∃ (t : CubeTag) (y : G.Dart),
      (t = CubeTag.CTn ∨ t = CubeTag.CTen ∨ t = CubeTag.CTf ∨ t = CubeTag.CTnf) ∧
      (cubeFace G)^[n] (CubeTag.CTf, x) = (t, y) := by
  induction' n with n ih generalizing x;
  · exact ⟨ _, _, Or.inr <| Or.inr <| Or.inl rfl, rfl ⟩;
  · rcases ih x with ⟨ t, y, h, h' ⟩ ; rcases h with ( rfl | rfl | rfl | rfl ) <;> simp_all +decide [ Function.iterate_succ_apply' ] ;
    · exact Or.inr <| Or.inl ⟨ _, rfl ⟩;
    · exact Or.inr <| Or.inr <| Or.inl ⟨ _, rfl ⟩;
    · exact Or.inr <| Or.inr <| Or.inr <| ⟨ _, rfl ⟩;
    · exact Or.inl ⟨ _, rfl ⟩

/-
If (CTnf, x) is face-connected to (CTen, y) in cube G, then cface G x y.
-/
private theorem cubeFace_CTnf_to_CTen (G : Hypermap) (x y : G.Dart) (n : ℕ)
    (hn : (cubeFace G)^[n] (CubeTag.CTnf, x) = (CubeTag.CTen, y)) :
    cface G x y := by
  -- If (CTnf, x) is face-connected to (CTen, y) in cube G, then cface G x y follows from the structure of the face orbit.
  have h_orbit : ∀ m : ℕ, (cubeFace G)^[m+2] (CubeTag.CTnf, x) = (cubeFace G)^[m] (CubeTag.CTen, G.face x) := by
    unfold Hypermap.cubeFace; aesop;
  rcases n with ( _ | _ | n ) <;> simp_all +decide [ Function.iterate_succ_apply' ];
  · cases hn;
  · -- By cubeFace_CTen_cface, we have cface G (face x) y.
    have h_cface_face : cface G (G.face x) y := by
      obtain ⟨ t, y, ht, hy, hxy ⟩ := cubeFace_CTen_cface G ( G.face x ) n; aesop;
    obtain ⟨ m, hm ⟩ := h_cface_face;
    exact ⟨ m + 1, hm ⟩

/-- Forward direction: Bridgeless G → Bridgeless (cube G) -/
private theorem bridgeless_cube_fwd (G : Hypermap) (hB : Bridgeless G) :
    Bridgeless (cube G) := by
  intro ⟨t, x⟩ ⟨n, hn⟩
  -- hn : (cube G).face^[n] (t, x) = (cube G).edge (t, x)
  -- i.e., (cubeFace G)^[n] (t, x) = cubeEdge G (t, x)
  change (cubeFace G)^[n] (t, x) = cubeEdge G (t, x) at hn
  cases t with
  | CTn =>
    -- cubeEdge(CTn, x) = (CTfe, x)
    simp [cubeEdge] at hn
    obtain ⟨y, hy⟩ := cubeFace_tag_mixed G x n
    rcases hy with h | h | h | h <;> rw [h] at hn <;> simp at hn
  | CTen =>
    -- cubeEdge(CTen, x) = (CTnf, edge x)
    simp [cubeEdge] at hn
    obtain ⟨t', y, _, heq, hcf⟩ := cubeFace_CTen_cface G x n
    rw [heq] at hn
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hn
    exact hB x hcf
  | CTf =>
    -- cubeEdge(CTf, x) = (CTe, node(face x))
    simp [cubeEdge] at hn
    obtain ⟨t', y, ht', heq⟩ := cubeFace_CTf_mixed G x n
    rw [heq] at hn
    rcases ht' with rfl | rfl | rfl | rfl <;> simp at hn
  | CTnf =>
    -- cubeEdge(CTnf, x) = (CTen, node(face x))
    simp [cubeEdge] at hn
    have hcf := cubeFace_CTnf_to_CTen G x (G.node (G.face x)) n hn
    -- cface G x (node(face x))
    -- By cface_sym: cface G (node(face x)) x
    have hcf' := cface_sym x (G.node (G.face x)) hcf
    -- edge(node(face x)) = x by faceK
    have hfK : G.edge (G.node (G.face x)) = x := faceK x
    -- So cface G (node(face x)) (edge(node(face x)))
    have : cface G (G.node (G.face x)) (G.edge (G.node (G.face x))) := by rwa [hfK]
    exact hB (G.node (G.face x)) this
  | CTe =>
    -- cubeEdge(CTe, x) = (CTf, edge x)
    simp [cubeEdge] at hn
    obtain ⟨y, hy⟩ := cubeFace_tag_edge G x n
    rw [hy] at hn; simp at hn
  | CTfe =>
    -- cubeEdge(CTfe, x) = (CTn, x)
    simp [cubeEdge] at hn
    obtain ⟨y, hy⟩ := cubeFace_tag_fe G x n
    rw [hy] at hn; simp at hn

/-
Reverse direction: Bridgeless (cube G) → Bridgeless G
-/
private theorem bridgeless_cube_rev (G : Hypermap) (hB : Bridgeless (cube G)) :
    Bridgeless G := by
  contrapose! hB; simp_all +decide [ Bridgeless ] ;
  obtain ⟨ x, n, hn ⟩ := hB; use ( CubeTag.CTen, x ) ; use 4 * n + 2; simp_all +decide [ Function.iterate_succ_apply' ] ;
  have h_cubeFace_iter_CTen : ∀ k : ℕ, (Hypermap.cubeFace G)^[4 * k] (CubeTag.CTen, x) = (CubeTag.CTen, G.face^[k] x) ∧ (Hypermap.cubeFace G)^[4 * k + 1] (CubeTag.CTen, x) = (CubeTag.CTf, G.face^[k] x) ∧ (Hypermap.cubeFace G)^[4 * k + 2] (CubeTag.CTen, x) = (CubeTag.CTnf, G.face^[k] x) ∧ (Hypermap.cubeFace G)^[4 * k + 3] (CubeTag.CTen, x) = (CubeTag.CTn, G.face^[k + 1] x) :=
    fun k => cubeFace_iter_CTen G x k;
  unfold Hypermap.cube at *; aesop;

/-- Bridgelessness is preserved by the cube construction. -/
theorem bridgeless_cube (G : Hypermap) : Bridgeless G ↔ Bridgeless (cube G) :=
  ⟨bridgeless_cube_fwd G, bridgeless_cube_rev G⟩

/-
If cube G is four-colorable, then G is four-colorable.
-/
theorem cube_colorable (G : Hypermap) : FourColorable (cube G) → FourColorable G := by
  -- Assume cube G has a coloring k
  rintro ⟨k, h_color⟩
  use fun x => k (CubeTag.CTn, x);
  cases h_color;
  unfold Hypermap.cube at *;
  unfold Hypermap.cubeEdge at *;
  unfold Hypermap.cubeFace at *;
  constructor;
  · grind;
  · grind

end Hypermap
