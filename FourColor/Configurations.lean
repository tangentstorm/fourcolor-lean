/-
Copyright (c) 2006-2018 Microsoft Corporation and Inria (Coq version).
Lean 4 port of the Four Color Theorem formalization.

The 633 reducible configurations used in the Four Color Theorem proof.
In the Coq version, each configuration is encoded as a compact data structure
(`cfmap`) and its reducibility is verified by computational reflection across
~100 job files, grouped into 10 task batches by `reducibility.v`.

This file defines the configuration infrastructure and states the key
reducibility results.
-/
import FourColor.Hypermap
import FourColor.Geometry
import FourColor.Coloring

set_option maxHeartbeats 400000

open Hypermap

namespace FourColor

/-! ## Configuration map representation -/

/-- Steps for building a configuration map. -/
inductive CfStep : Type where
  | CfR : Nat → CfStep   -- rotate
  | CfY : CfStep          -- add a Y-fan
  | CfH : CfStep          -- add an H-edge
  | CfU : CfStep          -- add a U-face
  deriving DecidableEq, Repr

/-- A configuration map specification is a list of construction steps. -/
abbrev CfMap := List CfStep

/-! ## The 633 configurations (configurations.v) -/

/-- The list of all 633 configurations used in the proof.
    In the Coq formalization, these are explicitly enumerated in
    configurations.v as `cf001`, …, `cf633`. -/
noncomputable def theConfigs : List CfMap := by
  sorry

/-- The number of configurations. -/
theorem theConfigs_length : theConfigs.length = 633 := by
  sorry

/-! ## Reducibility (cfreducible.v) -/

/-- A configuration is C-reducible: its coloring space is a subset of the
    Kempe closure of the coloring space of any embedding. This is verified
    computationally for each configuration in the job files. -/
def CfReducible (cf : CfMap) : Prop := by
  sorry

/-- The global reducibility statement: all configurations are C-reducible.
    In the Coq version, this is proved by large-scale computational
    reflection across ~100 job files. -/
def Reducibility : Prop :=
  ∀ cf ∈ theConfigs, CfReducible cf

/-! ### Per-batch reducibility (the 10 task files of `reducibility.v`)

The Rocq `the_reducibility` proof concatenates 10 batch lemmas
(`red000to214`, …, `red588to633`), each in its own task file. We mirror that
structure here: each batch is a sorry covering a contiguous index range; the
combined `the_reducibility` simply walks the index of `cf` to the right
batch. -/

/-- A configuration occurring at index `i` of `theConfigs` with `lo ≤ i < hi`
    is C-reducible. -/
def TaskReducibility (lo hi : ℕ) : Prop :=
  ∀ i, lo ≤ i → i < hi → ∀ h : i < theConfigs.length,
    CfReducible (theConfigs.get ⟨i, h⟩)

theorem red_000_to_214 : TaskReducibility 0 214 := sorry      -- task001to214.v
theorem red_214_to_234 : TaskReducibility 214 234 := sorry    -- task215to234.v
theorem red_234_to_282 : TaskReducibility 234 282 := sorry    -- task235to282.v
theorem red_282_to_302 : TaskReducibility 282 302 := sorry    -- task283to302.v
theorem red_302_to_322 : TaskReducibility 302 322 := sorry    -- task303to322.v
theorem red_322_to_485 : TaskReducibility 322 485 := sorry    -- task323to485.v
theorem red_485_to_506 : TaskReducibility 485 506 := sorry    -- task486to506.v
theorem red_506_to_541 : TaskReducibility 506 541 := sorry    -- task507to541.v
theorem red_541_to_588 : TaskReducibility 541 588 := sorry    -- task542to588.v
theorem red_588_to_633 : TaskReducibility 588 633 := sorry    -- task589to633.v

/-- The reducibility theorem: all 633 configurations are C-reducible.

    Combines the 10 per-batch reducibility lemmas. (Rocq `the_reducibility`
    in `reducibility.v` does the same thing using `cat_reducible_range`.) -/
theorem the_reducibility : Reducibility := by
  intro cf hcf
  -- `cf ∈ theConfigs` implies `cf = theConfigs.get ⟨i, h⟩` for some `i`.
  obtain ⟨i, h, rfl⟩ := List.mem_iff_get.mp hcf
  have hlt : i.val < 633 := theConfigs_length ▸ i.isLt
  -- Dispatch to the appropriate task batch by `i`.
  rcases lt_or_ge i.val 214 with h1 | h1
  · exact red_000_to_214 i.val (Nat.zero_le _) h1 i.isLt
  rcases lt_or_ge i.val 234 with h2 | h2
  · exact red_214_to_234 i.val h1 h2 i.isLt
  rcases lt_or_ge i.val 282 with h3 | h3
  · exact red_234_to_282 i.val h2 h3 i.isLt
  rcases lt_or_ge i.val 302 with h4 | h4
  · exact red_282_to_302 i.val h3 h4 i.isLt
  rcases lt_or_ge i.val 322 with h5 | h5
  · exact red_302_to_322 i.val h4 h5 i.isLt
  rcases lt_or_ge i.val 485 with h6 | h6
  · exact red_322_to_485 i.val h5 h6 i.isLt
  rcases lt_or_ge i.val 506 with h7 | h7
  · exact red_485_to_506 i.val h6 h7 i.isLt
  rcases lt_or_ge i.val 541 with h8 | h8
  · exact red_506_to_541 i.val h7 h8 i.isLt
  rcases lt_or_ge i.val 588 with h9 | h9
  · exact red_541_to_588 i.val h8 h9 i.isLt
  exact red_588_to_633 i.val h9 hlt i.isLt

end FourColor
