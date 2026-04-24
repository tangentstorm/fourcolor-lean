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

/-- The genus of the cube equals the genus of the original.
    This is the key structural result about the cube construction.
    Proved by computing the Euler formula components for cube G:
    - |cube G| = 6|G|
    - fcardEdge(cube G) = 3|G|  (since cube is plain)
    - fcardNode(cube G) = 2|G|  (since cube is cubic)
    - fcardFace(cube G) = fcardEdge G + fcardNode G + fcardFace G = eulerRhs G
    - nComp(cube G) = nComp G
    Corresponds to `genus_cube` in Coq's cube.v. -/
theorem card_CubeTag : Fintype.card CubeTag = 6 := by decide

theorem card_cube_dart (G : Hypermap) :
    Fintype.card (cube G).Dart = 6 * Fintype.card G.Dart := by
  simp [cube, Fintype.card_prod, card_CubeTag]

/-
In a plain hypermap where every edge orbit has exactly 2 elements,
    the number of edge orbits equals half the number of darts.
-/
theorem fcardEdge_of_plain (G : Hypermap) (hP : Plain G) :
    fcardEdge G = Fintype.card G.Dart / 2 := by
  -- Each cycle in `edgePerm` has length exactly 2.
  have h_cycle_length : ∀ c ∈ (edgePerm G).cycleFactorsFinset, c.support.card = 2 := by
    intro c hc;
    -- Since $c$ is a cycle in the edge permutation, and $G$ is plain, $c$ must be a 2-cycle.
    have h_cycle_2 : c ^ 2 = 1 := by
      have h_edgePerm_sq : G.edgePerm ^ 2 = 1 := by
        ext x
        show G.edgePerm (G.edgePerm x) = x
        have := hP x
        simp [edgePerm]; exact this.1
      rw [Equiv.Perm.mem_cycleFactorsFinset_iff] at hc
      obtain ⟨hc_cyc, hc_sub⟩ := hc
      ext x
      show c (c x) = x
      by_cases hx : x ∈ c.support
      · -- x ∈ support: c agrees with edgePerm here, iterate twice uses edgePerm^2 = 1.
        have hcx_mem : c x ∈ c.support := Equiv.Perm.apply_mem_support.mpr hx
        rw [hc_sub (c x) hcx_mem, hc_sub x hx]
        have := congr_fun (congr_arg (fun p : Equiv.Perm G.Dart => (p : _ → _)) h_edgePerm_sq) x
        simpa [sq, Equiv.Perm.mul_apply] using this
      · -- x ∉ support: c x = x.
        have hxe : c x = x := by
          by_contra hne
          exact hx (Equiv.Perm.mem_support.mpr hne)
        rw [hxe, hxe]
    have h_cycle_2 : ∀ {σ : Equiv.Perm G.Dart}, σ.IsCycle → σ ^ 2 = 1 → σ.support.card = 2 := by
      intros σ hσ hσ_sq
      -- A cycle has support.card ≥ 2, and from σ^2 = 1 we get support.card ∣ 2.
      have h_dvd : σ.support.card ∣ 2 := by
        have := hσ.orderOf
        exact this ▸ orderOf_dvd_of_pow_eq_one hσ_sq
      have h_ge : 2 ≤ σ.support.card := hσ.two_le_card_support
      have h_le : σ.support.card ≤ 2 := Nat.le_of_dvd (by decide) h_dvd
      omega
    exact h_cycle_2
      ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1) ‹_›;
  -- Since each cycle has length 2, the total number of darts is twice the number of cycles.
  have h_total_darts : (Fintype.card G.Dart) = 2 * (edgePerm G).cycleFactorsFinset.card := by
    have h_total_darts : ∑ c ∈ (edgePerm G).cycleFactorsFinset, c.support.card = Fintype.card G.Dart := by
      convert Equiv.Perm.sum_cycleType G.edgePerm using 1;
      -- edgePerm.support = univ, so it equals the universal set.
      refine congr_arg Finset.card ?_
      ext x; simp [hP]; exact (hP x).2;
    rw [ ← h_total_darts, Finset.sum_congr rfl h_cycle_length, Finset.sum_const, smul_eq_mul, mul_comm ];
  have h_support : (edgePerm G).support = Finset.univ := by
    ext x; simp [hP];
    exact hP x |>.2;
  -- fcardEdge G = |cycleFactorsFinset| + (|Dart| - |support|).
  -- |support| = |univ| = |Dart|, so the fixed-point count is 0, and
  -- |Dart| = 2 * |cycleFactorsFinset|, so the result is |Dart| / 2.
  unfold Hypermap.fcardEdge numOrbits
  rw [h_support, Finset.card_univ, h_total_darts, Nat.sub_self,
      Nat.add_zero, Nat.mul_div_cancel_left _ (by decide : (0:ℕ) < 2)]

/-
In a cubic hypermap where every node orbit has exactly 3 elements,
    the number of node orbits equals a third of the number of darts.
-/
theorem fcardNode_of_cubic (G : Hypermap) (hC : Cubic G) :
    fcardNode G = Fintype.card G.Dart / 3 := by
  unfold Hypermap.fcardNode Hypermap.numOrbits;
  -- Since the node permutation is a product of disjoint 3-cycles covering all darts, each cycle has length exactly 3.
  have h_node_cycle_length : ∀ c ∈ G.nodePerm.cycleType, c = 3 := by
    intro c hc
    have h_cycle_length : c ∣ 3 := by
      have h_cycle_length : G.nodePerm ^ 3 = 1 := by
        ext x; exact (by
        exact hC x |>.1);
      exact orderOf_dvd_iff_pow_eq_one.mpr h_cycle_length |> fun h => dvd_trans ( by simpa using Equiv.Perm.dvd_of_mem_cycleType hc ) h;
    have := Nat.le_of_dvd ( by decide ) h_cycle_length; interval_cases c <;> simp_all +decide ;
    simp_all +decide [ Equiv.Perm.mem_cycleType_iff ];
    obtain ⟨ c, τ, h₁, h₂, h₃, h₄ ⟩ := hc; have := h₃.orderOf; simp_all +decide [ Equiv.Perm.Disjoint ] ;
  have h_node_cycle_count : (G.nodePerm.cycleType.sum : ℕ) = 3 * G.nodePerm.cycleFactorsFinset.card := by
    rw [ Multiset.eq_replicate_of_mem h_node_cycle_length ] ; norm_num ; ring;
    rw [ Equiv.Perm.cycleType_def ];
    simp +decide [ Function.comp ];
  have h_node_support_card : G.nodePerm.support.card = Fintype.card G.Dart := by
    refine' Finset.card_bij ( fun x hx => x ) _ _ _ <;> simp +decide [ hC ];
    exact fun x => by simpa [ Hypermap.nodePerm ] using hC x |>.2.1;
  -- support.card = |Dart| (no fixed points), and cycleType.sum = 3 * |cycleFactorsFinset|,
  -- so |cycleFactorsFinset| = |Dart| / 3.
  have hsum := Equiv.Perm.sum_cycleType G.nodePerm
  rw [h_node_support_card, Nat.sub_self, Nat.add_zero]
  rw [h_node_support_card] at hsum
  rw [← hsum, h_node_cycle_count, Nat.mul_div_cancel_left _ (by decide : (0:ℕ) < 3)]

/-- The number of face orbits in the cube equals the Euler rhs of G.
    Face orbits decompose into three types:
    - {CTn, CTen, CTf, CTnf} orbits correspond to face orbits of G
    - {CTe} orbits correspond to edge orbits of G
    - {CTfe} orbits correspond to node orbits of G -/
theorem fcardFace_cube (G : Hypermap) :
    fcardFace (cube G) = eulerRhs G := by
  sorry

/-
Every dart (t, x) in cube G is glink-connected to (CTnf, x).
    This is proved by exhibiting explicit glink paths for each tag.
-/
theorem cube_glink_to_CTnf (G : Hypermap) (t : CubeTag) (x : G.Dart) :
    Relation.EqvGen (glink (cube G)) (t, x) (CubeTag.CTnf, x) := by
  cases t;
  all_goals unfold Hypermap.cube; simp +decide [ Hypermap.glink ];
  exact Relation.EqvGen.trans _ _ _ ( Relation.EqvGen.rel _ _ ( Or.inr ( Or.inr rfl ) ) ) ( Relation.EqvGen.trans _ _ _ ( Relation.EqvGen.rel _ _ ( Or.inr ( Or.inr rfl ) ) ) ( Relation.EqvGen.rel _ _ ( Or.inr ( Or.inr rfl ) ) ) );
  · exact Relation.EqvGen.trans _ _ _ ( Relation.EqvGen.rel _ _ ( Or.inr ( Or.inr rfl ) ) ) ( Relation.EqvGen.rel _ _ ( Or.inr ( Or.inr rfl ) ) );
  · apply Relation.EqvGen.rel; simp [Hypermap.glink];
    exact Or.inr <| Or.inr <| by unfold Hypermap.cubeFace; rfl;
  · exact Relation.EqvGen.refl _;
  · -- By definition of `cubeNode`, we have `cubeNode (CubeTag.CTe, x) = (CubeTag.CTf, x)`.
    have h_cubeNode_CTe : G.cubeNode (CubeTag.CTe, x) = (CubeTag.CTf, x) := rfl
    exact Relation.EqvGen.trans _ _ _ ( Relation.EqvGen.rel _ _ ( Or.inr ( Or.inl h_cubeNode_CTe ) ) ) ( Relation.EqvGen.rel _ _ ( Or.inr ( Or.inr rfl ) ) );
  · -- By definition of glink, we can connect (CTfe, x) to (CTn, x) via the edge function.
    have h_edge : Relation.EqvGen G.cube.glink (CubeTag.CTfe, x) (CubeTag.CTn, x) := by
      exact Relation.EqvGen.rel _ _ ( Or.inl rfl );
    -- By definition of glink, we can connect (CTn, x) to (CTen, x) via the face function.
    have h_face1 : Relation.EqvGen G.cube.glink (CubeTag.CTn, x) (CubeTag.CTen, x) := by
      apply Relation.EqvGen.rel;
      exact Or.inr <| Or.inr <| by rfl;
    -- By definition of glink, we can connect (CTen, x) to (CTf, x) via the face function.
    have h_face2 : Relation.EqvGen G.cube.glink (CubeTag.CTen, x) (CubeTag.CTf, x) := by
      apply Relation.EqvGen.rel;
      exact Or.inr <| Or.inr <| by rfl;
    exact Relation.EqvGen.trans _ _ _ h_edge ( Relation.EqvGen.trans _ _ _ h_face1 ( Relation.EqvGen.trans _ _ _ h_face2 ( Relation.EqvGen.rel _ _ ( Or.inr ( Or.inr rfl ) ) ) ) )

/-
If x and y are glink-related in G, then (CTnf, x) and (CTnf, y)
    are glink-related in cube G (via edge/node/face of cube).
-/
theorem cube_glink_lift (G : Hypermap) (x y : G.Dart) :
    Relation.EqvGen (glink G) x y →
    Relation.EqvGen (glink (cube G)) (CubeTag.CTnf, x) (CubeTag.CTnf, y) := by
  intro h
  induction' h with x y hxy ih1 ih2 ih3;
  · obtain h | h | h := hxy;
    · have h_chain : Relation.EqvGen G.cube.glink (CubeTag.CTnf, x) (CubeTag.CTen, x) := by
        apply Relation.EqvGen.symm;
        exact cube_glink_to_CTnf G CubeTag.CTen x
      have h_chain : Relation.EqvGen G.cube.glink (CubeTag.CTen, x) (CubeTag.CTnf, y) := by
        apply Relation.EqvGen.rel;
        -- cubeEdge (CTen, x) = (CTnf, G.edge x) = (CTnf, y) since h : G.edge x = y
        exact Or.inl (by subst h; rfl);
      exact Relation.EqvGen.trans _ _ _ ‹_› ‹_›;
    · have h_chain2 : Relation.EqvGen G.cube.glink (CubeTag.CTn, x) (CubeTag.CTen, y) := by
        apply Relation.EqvGen.rel;
        -- cubeNode (CTn, x) = (CTen, G.node x) = (CTen, y) since h : G.node x = y
        exact Or.inr <| Or.inl <| by subst h; rfl;
      grind +suggestions;
    · have h_cubeFace : G.cube.face (CubeTag.CTnf, x) = (CubeTag.CTn, y) := by
        -- cubeFace (CTnf, x) = (CTn, G.face x) = (CTn, y) since h : G.face x = y
        subst h; rfl;
      have h_cube_glink_to_CTnf : Relation.EqvGen G.cube.glink (CubeTag.CTn, y) (CubeTag.CTnf, y) := by
        grind +suggestions;
      exact Relation.EqvGen.trans _ _ _ ( Relation.EqvGen.rel _ _ <| by tauto ) h_cube_glink_to_CTnf;
  · exact Relation.EqvGen.refl _;
  · exact Relation.EqvGen.symm _ _ ‹_›;
  · exact Relation.EqvGen.trans _ _ _ ‹_› ‹_›

/-
The number of connected components is preserved by the cube construction.
-/
theorem nComp_cube (G : Hypermap) :
    nComp (cube G) = nComp G := by
  -- By definition of quotient, we need to show that each equivalence class in the cube's quotient maps to a unique equivalence class in G's quotient, and vice versa.
  have h_bij : ∀ (x y : (CubeTag × G.Dart)), (Relation.EqvGen (glink (cube G)) x y) ↔ (Relation.EqvGen (glink G) x.2 y.2) := by
    intro x y;
    constructor;
    · intro hxy
      have h_glink : ∀ x y : CubeTag × G.Dart, glink (cube G) x y → Relation.EqvGen (glink G) x.2 y.2 := by
        rintro ⟨ t₁, x₁ ⟩ ⟨ t₂, x₂ ⟩ ( h | h | h ) <;> simp_all +decide [ Hypermap.glink ];
        · cases t₁ <;> cases t₂ <;> simp_all +decide [ Hypermap.cube ];
          all_goals unfold Hypermap.cubeEdge at h; simp_all +decide [ Hypermap.glink ] ;
          any_goals exact Relation.EqvGen.refl _;
          · exact Relation.EqvGen.rel _ _ ( by tauto );
          · apply Relation.EqvGen.trans;
            exact Relation.EqvGen.rel _ _ ( Or.inr <| Or.inr <| by tauto );
            exact Relation.EqvGen.rel _ _ ( Or.inr <| Or.inl <| by tauto );
          · apply Relation.EqvGen.trans;
            exact Relation.EqvGen.rel _ _ ( Or.inr <| Or.inr <| by tauto );
            exact Relation.EqvGen.rel _ _ ( Or.inr <| Or.inl <| by tauto );
          · exact Relation.EqvGen.rel _ _ ( by tauto );
        · rcases t₁ with ( _ | _ | _ | _ | _ | _ ) <;> rcases t₂ with ( _ | _ | _ | _ | _ | _ ) <;> simp_all +decide [ Hypermap.cube ];
          all_goals unfold Hypermap.cubeNode at h; simp_all +decide [ Hypermap.glink ] ;
          any_goals exact Relation.EqvGen.refl _;
          · exact Relation.EqvGen.rel _ _ ( by tauto );
          · exact Relation.EqvGen.rel _ _ ( by tauto );
          · apply Relation.EqvGen.trans;
            exact Relation.EqvGen.rel _ _ ( Or.inr <| Or.inr <| by tauto );
            exact Relation.EqvGen.rel _ _ ( Or.inr <| Or.inl <| by tauto );
          · rw [ ← h ];
            apply Relation.EqvGen.trans;
            exact Relation.EqvGen.rel _ _ ( Or.inl rfl );
            exact Relation.EqvGen.rel _ _ ( Or.inr <| Or.inr rfl );
        · cases t₁ <;> cases t₂ <;> simp_all +decide [ Hypermap.cube ];
          all_goals unfold Hypermap.cubeFace at h; simp_all +decide [ Hypermap.glink ] ;
          any_goals exact Relation.EqvGen.refl _;
          · exact Relation.EqvGen.rel _ _ ( by tauto );
          · exact Relation.EqvGen.rel _ _ ( by tauto );
          · exact Relation.EqvGen.rel _ _ ( by tauto );
      induction hxy;
      · exact h_glink _ _ ‹_›;
      · exact Relation.EqvGen.refl _;
      · exact Relation.EqvGen.symm _ _ ‹_›
      · exact Relation.EqvGen.trans _ _ _ ‹_› ‹_›;
    · -- By definition of $cube$, we know that if $x.2$ and $y.2$ are related by $glink$ in $G$, then $x$ and $y$ are related by $glink$ in $cube G$.
      have h_rel : ∀ (x y : G.Dart), Relation.EqvGen G.glink x y → Relation.EqvGen (cube G).glink (CubeTag.CTnf, x) (CubeTag.CTnf, y) := by
        grind +suggestions
      generalize_proofs at *; (
      grind +suggestions)
  generalize_proofs at *; (
  convert Fintype.card_congr ?_ using 1;
  refine' Equiv.ofBijective ( fun x => Quotient.map' ( fun y => y.2 ) ( fun y₁ y₂ hy => ?_ ) x ) ⟨ fun x y hxy => ?_, fun x => ?_ ⟩;
  exact h_bij _ _ |>.1 hy;
  · obtain ⟨ a, rfl ⟩ := Quotient.exists_rep x; obtain ⟨ b, rfl ⟩ := Quotient.exists_rep y; simp_all +decide [ Quotient.eq ] ;
    exact h_bij _ _ |>.2 hxy;
  · obtain ⟨ y, rfl ⟩ := Quotient.exists_rep x; exact ⟨ ⟦ ( CubeTag.CTnf, y ) ⟧, rfl ⟩ ;)

theorem genus_cube (G : Hypermap) : genus (cube G) = genus G := by
  unfold Hypermap.genus;
  unfold Hypermap.eulerLhs Hypermap.eulerRhs;
  rw [ fcardEdge_of_plain _ ( plain_cube G ), fcardNode_of_cubic _ ( cubic_cube G ), fcardFace_cube ];
  rw [ nComp_cube, card_cube_dart ];
  unfold Hypermap.eulerRhs; omega;

/-- Planarity is preserved by the cube construction. -/
theorem planar_cube (G : Hypermap) : Planar G ↔ Planar (cube G) := by
  unfold Planar
  rw [genus_cube]

-- `cface_sym` is now provided centrally in Geometry.lean (ported from `cfaceC`
-- in geometry.v). The Cube module re-uses the generic version.

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

/-- In cube G, face iteration acting on (CTe, x) darts just iterates G.edge
    in the second component. So the face-orbit of (CTe, x) projects 1-to-1
    onto the edge-orbit of x. -/
theorem cubeFace_CTe_iter (G : Hypermap) (x : G.Dart) (n : ℕ) :
    (cubeFace G)^[n] (CubeTag.CTe, x) = (CubeTag.CTe, G.edge^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; simp [cubeFace, Function.iterate_succ_apply']

/-- In cube G, face iteration acting on (CTfe, x) darts just iterates G.node
    in the second component. So the face-orbit of (CTfe, x) projects 1-to-1
    onto the node-orbit of x. -/
theorem cubeFace_CTfe_iter (G : Hypermap) (x : G.Dart) (n : ℕ) :
    (cubeFace G)^[n] (CubeTag.CTfe, x) = (CubeTag.CTfe, G.node^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; simp [cubeFace, Function.iterate_succ_apply']

/-- The cube face orbit of (CTe, x) stays at tag CTe. -/
theorem cubeFace_tag_preserves_CTe (G : Hypermap) (x : G.Dart) (n : ℕ) :
    ((cubeFace G)^[n] (CubeTag.CTe, x)).1 = CubeTag.CTe := by
  rw [cubeFace_CTe_iter]

/-- The cube face orbit of (CTfe, x) stays at tag CTfe. -/
theorem cubeFace_tag_preserves_CTfe (G : Hypermap) (x : G.Dart) (n : ℕ) :
    ((cubeFace G)^[n] (CubeTag.CTfe, x)).1 = CubeTag.CTfe := by
  rw [cubeFace_CTfe_iter]

/-- The second component of iterating cubeFace on (CTe, x) is `G.edge^[n] x`. -/
theorem cubeFace_snd_CTe (G : Hypermap) (x : G.Dart) (n : ℕ) :
    ((cubeFace G)^[n] (CubeTag.CTe, x)).2 = G.edge^[n] x := by
  rw [cubeFace_CTe_iter]

/-- The second component of iterating cubeFace on (CTfe, x) is `G.node^[n] x`. -/
theorem cubeFace_snd_CTfe (G : Hypermap) (x : G.Dart) (n : ℕ) :
    ((cubeFace G)^[n] (CubeTag.CTfe, x)).2 = G.node^[n] x := by
  rw [cubeFace_CTfe_iter]

/-
Face iteration on CTfe stays in CTfe.
-/
private theorem cubeFace_tag_fe (G : Hypermap) (x : G.Dart) (n : ℕ) :
    ∃ y, (cubeFace G)^[n] (CubeTag.CTfe, x) = (CubeTag.CTfe, y) := by
  induction n <;> simp_all +decide [ Function.iterate_succ_apply' ];
  obtain ⟨ y, hy ⟩ := ‹_›; exact ⟨ G.node y, by rw [hy]; rfl ⟩;

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

/-- Face iteration from (CTn, x) follows the 4-periodic pattern, shifted
    from CTen by one step. -/
private theorem cubeFace_iter_CTn (G : Hypermap) (x : G.Dart) (k : ℕ) :
    (cubeFace G)^[4 * k] (CubeTag.CTn, x) = (CubeTag.CTn, G.face^[k] x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [show 4 * (k + 1) = 4 * k + 4 from by ring, Function.iterate_add_apply]
    simp only [Function.iterate_succ_apply', Function.iterate_zero, id, cubeFace]
    rw [(Function.Commute.iterate_self G.face k).symm.eq x]
    exact ih (G.face x)

/-- Face iteration from (CTf, x) follows the 4-periodic pattern, shifted
    from CTen by two steps. -/
private theorem cubeFace_iter_CTf (G : Hypermap) (x : G.Dart) (k : ℕ) :
    (cubeFace G)^[4 * k] (CubeTag.CTf, x) = (CubeTag.CTf, G.face^[k] x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [show 4 * (k + 1) = 4 * k + 4 from by ring, Function.iterate_add_apply]
    simp only [Function.iterate_succ_apply', Function.iterate_zero, id, cubeFace]
    rw [(Function.Commute.iterate_self G.face k).symm.eq x]
    exact ih (G.face x)

/-- Face iteration from (CTnf, x) follows the 4-periodic pattern, shifted
    from CTen by three steps. -/
private theorem cubeFace_iter_CTnf (G : Hypermap) (x : G.Dart) (k : ℕ) :
    (cubeFace G)^[4 * k] (CubeTag.CTnf, x) = (CubeTag.CTnf, G.face^[k] x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [show 4 * (k + 1) = 4 * k + 4 from by ring, Function.iterate_add_apply]
    simp only [Function.iterate_succ_apply', Function.iterate_zero, id, cubeFace]
    rw [(Function.Commute.iterate_self G.face k).symm.eq x]
    exact ih (G.face x)

/-
Face orbit of (CTen, x) only contains darts with tags in {CTn, CTen, CTf, CTnf}
    and second component in the face orbit of x.
-/
private theorem cubeFace_CTen_cface (G : Hypermap) (x : G.Dart) (n : ℕ) :
    ∃ (t : CubeTag) (y : G.Dart),
      t ∈ ({CubeTag.CTn, CubeTag.CTen, CubeTag.CTf, CubeTag.CTnf} : Set CubeTag) ∧
      (cubeFace G)^[n] (CubeTag.CTen, x) = (t, y) ∧
      cface G x y := by
  rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> simp +decide [ *, Function.iterate_succ_apply' ] at *;
  · rcases Nat.even_or_odd' k with ⟨ k, rfl | rfl ⟩ <;> simp +decide [ *, Function.iterate_mul ] at *;
    · refine Or.inr <| Or.inl ⟨ G.face^[k] x, ?_, ?_ ⟩;
      · refine' Nat.recOn k _ _ <;> simp_all +decide [ Function.iterate_succ_apply' ];
        intro _ _; simp [cubeFace]
      · exact ⟨ k, rfl ⟩;
    · refine' Or.inr <| Or.inr <| Or.inr ⟨ _, _, _ ⟩;
      exact G.face^[k] x;
      · induction k <;> simp_all +decide [ Function.iterate_succ_apply' ];
        · simp [cubeFace]
        · unfold Hypermap.cubeFace; aesop;
      · exact ⟨ k, rfl ⟩;
  · induction k <;> simp_all +decide [ Nat.mul_succ, Function.iterate_succ_apply' ] ;
    · exact Or.inr <| Or.inr <| Or.inl ⟨ x, rfl, ⟨ 0, rfl ⟩ ⟩;
    · rename_i k hk; rcases hk with ( ⟨ y, hy, hy' ⟩ | ⟨ y, hy, hy' ⟩ | ⟨ y, hy, hy' ⟩ | ⟨ y, hy, hy' ⟩ ) <;> simp_all +decide ;
      · unfold Hypermap.cubeFace; simp +decide [ * ] ;
      · unfold Hypermap.cubeFace; simp +decide [ * ] ;
      · unfold Hypermap.cubeFace; simp +decide [ * ] ;
        exact ⟨ hy'.choose + 1, by simpa [ Function.iterate_succ_apply' ] using congr_arg G.face hy'.choose_spec ⟩;
      · unfold Hypermap.cubeFace; simp +decide [ * ] ;
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
    -- cubeFace (CTnf, x) = (CTn, G.face x); cubeFace (CTn, G.face x) = (CTen, G.face x).
    intro m
    rw [show m + 2 = m + 1 + 1 from rfl,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
    rfl
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
    have hcf' := cface_sym hcf
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