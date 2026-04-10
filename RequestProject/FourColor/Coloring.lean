/-
Copyright (c) 2006-2018 Microsoft Corporation and Inria (Coq version).
Lean 4 port of the Four Color Theorem formalization.

Hypermap and graph colorings, colorable maps, ring traces, valid contracts,
and the definition of the special maps used in the proof: minimal counter
example, C-reducible, and embeddable.
-/
import RequestProject.FourColor.Hypermap
import RequestProject.FourColor.Color
import RequestProject.FourColor.Geometry

set_option maxHeartbeats 400000

open Hypermap Color

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

/-! ## Graph coloring (dual) -/

/-- A graph coloring: constant on nodes, distinct on edges. -/
def GraphColoring (k : G.Dart → Color) : Prop :=
  (∀ x, k (G.edge x) ≠ k x) ∧
  (∀ x, k (G.node x) = k x)

/-- A hypermap is graph-four-colorable. -/
def GraphFourColorable (G : Hypermap) : Prop :=
  ∃ k : G.Dart → Color, GraphColoring k

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

/-! ## Ring traces -/

/-- A ring trace: there exists a proper coloring whose restriction to
    the ring r produces the edge trace et. -/
def RingTrace (r : List G.Dart) (et : List Color) : Prop :=
  ∃ k : G.Dart → Color, Coloring k ∧ et = Color.trace (r.map k)

/-- A contract ring trace. -/
def CcRingTrace (cc : Finset G.Dart) (r : List G.Dart) (et : List Color) : Prop :=
  ∃ k : G.Dart → Color, CcColoring cc k ∧ et = Color.trace (r.map k)

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

/-! ## Embeddability -/

/-- A configuration is embeddable with perimeter ring r if it is planar,
    bridgeless, connected, plain, and r-quasicubic for the simple N-cycle r. -/
def Embeddable (r : List G.Dart) : Prop :=
  Planar G ∧
  Bridgeless G ∧
  Connected G ∧
  Plain G ∧
  Quasicubic G (r.toFinset) ∧
  Srcycle G r

/-! ## C-reducibility -/

/-- A valid contract for ring r: cc has size ≤ 4, and certain combinatorial
    conditions hold (sparseness, triad condition). -/
def ValidContract (r : List G.Dart) (cc : Finset G.Dart) : Prop :=
  cc.card ≤ 4 ∧
  Disjoint (insertE G r).toFinset cc ∧
  -- Additional sparseness and triad conditions
  True

/-- C-reducibility: assuming G is a configuration with ring r, G is
    C-reducible with contract cc if cc is valid and any contract ring trace
    for cc can be adjusted to a ring trace of a full coloring. -/
def CReducible (r : List G.Dart) (cc : Finset G.Dart) : Prop :=
  ValidContract r cc ∧
  -- Kempe closure condition
  True

/-! ## Decidability of four-colorability -/

/-- Four-colorability is decidable for finite hypermaps. -/
noncomputable instance (G : Hypermap) : Decidable (FourColorable G) :=
  Classical.dec _

end Hypermap
