/-
Copyright (c) 2006-2018 Microsoft Corporation and Inria (Coq version).
Lean 4 port of the Four Color Theorem formalization.

Chromograms: balanced symbol strings that encode Kempe-chain structure.
Ported from rocq/fourcolor/theories/proof/chromogram.v.
-/
import FourColor.Color

set_option linter.dupNamespace false

namespace FourColor.Chromogram

open Color

/-! ## Gram symbols and chromograms -/

/-- The four grammar symbols used to encode Kempe chains.
    Coq: chromogram.v:59 -/
inductive GramSymbol : Type where
  | Gpush : GramSymbol
  | Gskip : GramSymbol
  | Gpop0 : GramSymbol
  | Gpop1 : GramSymbol
  deriving DecidableEq, Repr

/-- A chromogram is a list of grammar symbols. -/
abbrev Chromogram := List GramSymbol

/-! ## Balanced chromograms -/

/-- A chromogram is balanced when the push/pop nesting depth returns to zero
    and the parity bit returns to `false`.
    `d` is the current nesting depth, `b0` the current parity bit.
    Coq: chromogram.v:78 -/
def gramBalanced (d : Nat) (b0 : Bool) : Chromogram → Bool
  | []              => decide (d = 0) && !b0
  | .Gpush :: w'    => gramBalanced (d + 1) b0 w'
  | .Gskip :: w'    => gramBalanced d (!b0) w'
  | .Gpop0 :: w'    => match d with | 0 => false | d' + 1 => gramBalanced d' b0 w'
  | .Gpop1 :: w'    => match d with | 0 => false | d' + 1 => gramBalanced d' (!b0) w'

/-! ## Chromogram matching

The matching relation between a color edge-trace and a chromogram,
mirroring the Coq definition at chromogram.v:88. Colors pair with
symbols as follows:

- `Color1` only pairs with `Gskip` (leaves `lb` unchanged).
- `Color2` pairs with `Gpush` (pushes `false`), `Gpop0` (requires head `false`),
  or `Gpop1` (requires head `true`).
- `Color3` pairs with `Gpush` (pushes `true`), `Gpop0` (requires head `true`),
  or `Gpop1` (requires head `false`).
- `Color0` never matches (it is the identity color, excluded from traces).
-/

/-- Matchable combinations of color + symbol + stack head, matching the
    Coq case analysis exactly. -/
def matchg : List Bool → List Color → Chromogram → Bool
  | [],       [],        []            => true
  | _ :: _,   [],        _             => false  -- nonempty lb at end
  | _,        [],        _ :: _        => false  -- et shorter than w
  | _,        _ :: _,    []            => false  -- et longer than w
  -- Color1 only pairs with Gskip, preserving lb.
  | lb,       Color1 :: et',  .Gskip :: w'      => matchg lb et' w'
  -- Color2 with Gpush: push `false`.
  | lb,       Color2 :: et',  .Gpush :: w'      => matchg (false :: lb) et' w'
  -- Color2 with Gpop0: head must be `false`.
  | false :: lb', Color2 :: et', .Gpop0 :: w'   => matchg lb' et' w'
  -- Color2 with Gpop1: head must be `true`.
  | true :: lb',  Color2 :: et', .Gpop1 :: w'   => matchg lb' et' w'
  -- Color3 with Gpush: push `true`.
  | lb,       Color3 :: et',  .Gpush :: w'      => matchg (true :: lb) et' w'
  -- Color3 with Gpop0: head must be `true`.
  | true :: lb',  Color3 :: et', .Gpop0 :: w'   => matchg lb' et' w'
  -- Color3 with Gpop1: head must be `false`.
  | false :: lb', Color3 :: et', .Gpop1 :: w'   => matchg lb' et' w'
  -- All other combinations fail.
  | _,        _ :: _,    _ :: _        => false

/-! ## Kempe closure -/

/-- A predicate on edge-traces is Kempe-closed when it is closed under
    edge-color permutation and under chromogram matching.
    Coq: chromogram.v:105 -/
def KempeClosed (P : List Color → Prop) : Prop :=
  ∀ et, P et →
    (∀ g : EdgePerm, P (et.map g.apply)) ∧
    (∃ w : Chromogram, matchg [] et w ∧ ∀ et', matchg [] et' w → P et')

/-- The Kempe co-closure of `P` at `et`: every Kempe-closed superset of `P`
    that contains `et` must intersect `P`.
    Coq: chromogram.v:111 -/
def KempeCoclosure (P : List Color → Prop) (et : List Color) : Prop :=
  ∀ P', KempeClosed P' → P' et → ∃ et', P et' ∧ P' et'

/-! ## TODO: deeper lemmas from chromogram.v

The following lemmas are left for a future port:
- `matchg_size` (chromogram.v:114)
- `matchg_memc0` (chromogram.v:123)
- `matchg_balanced` (chromogram.v:131)
- `balanced_inj` (chromogram.v:148)
- `match_etrace` (chromogram.v:160)
-/

end FourColor.Chromogram
