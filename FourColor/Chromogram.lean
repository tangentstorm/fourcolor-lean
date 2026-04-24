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

/-! ## Balance and matching lemmas -/

-- Coq: chromogram.v:78
@[simp] theorem gramBalanced_nil : gramBalanced 0 false [] = true := by rfl

/-
Coq: chromogram.v:114

If `matchg lb et w` holds, then `w` and `et` have the same length.
-/
theorem matchg_size {lb : List Bool} {et : List Color} {w : Chromogram}
    (h : matchg lb et w = true) : w.length = et.length := by
  induction' w with s w ih generalizing lb et;
  · cases et <;> cases lb <;> tauto;
  · rcases et with ( _ | ⟨ e, et ⟩ ) <;> rcases lb with ( _ | ⟨ b, lb ⟩ ) <;> simp_all +decide;
    · cases s <;> cases h;
    · cases s <;> cases h;
    · rcases e with ( _ | _ | _ | _ ) <;> rcases s with ( _ | _ | _ | _ ) <;> tauto;
    · rcases e with ( _ | _ | _ | _ ) <;> rcases s with ( _ | _ | _ | _ );
      all_goals cases b <;> cases lb <;> tauto

/-
Coq: chromogram.v:123

A matching trace never contains `Color0`.
-/
theorem matchg_memc0 {lb : List Bool} {et : List Color} {w : Chromogram}
    (h : matchg lb et w = true) : Color0 ∉ et := by
  revert et w lb;
  intros lb et w h_matchg
  induction' w with w_head w_tail ih generalizing lb et;
  · cases et <;> cases lb <;> tauto;
  · rcases et with ( _ | ⟨ c, et ⟩ ) <;> rcases lb with ( _ | ⟨ b, lb ⟩ ) <;> simp_all +decide;
    · rcases c with ( _ | _ | _ | _ | c ) <;> rcases w_head with ( _ | _ | _ | _ | w_head ) <;> tauto;
    · cases c <;> cases w_head <;> simp_all +decide;
      all_goals cases b <;> simp_all +decide [ matchg ];
      all_goals exact ih h_matchg;

/-
Coq: chromogram.v:148

`gramBalanced` determines the depth and parity uniquely.
-/
theorem balanced_inj {w : Chromogram} {n1 n2 : Nat} {b1 b2 : Bool}
    (h1 : gramBalanced n1 b1 w = true) (h2 : gramBalanced n2 b2 w = true) :
    n1 = n2 ∧ b1 = b2 := by
  induction' w with s w ih generalizing n1 n2 b1 b2;
  · cases n1 <;> cases n2 <;> cases b1 <;> cases b2 <;> trivial;
  · rcases s with ( _ | _ | _ | _ ) <;> simp +decide [ gramBalanced ] at h1 h2 ⊢;
    · obtain ⟨h, h'⟩ := ih h1 h2; exact ⟨by omega, h'⟩;
    · obtain ⟨h, h'⟩ := @ih n1 n2 (!b1) (!b2) h1 h2; exact ⟨h, Bool.not_inj h'⟩;
    · rcases n1 with ( _ | n1 ) <;> rcases n2 with ( _ | n2 ) <;> simp +decide at h1 h2 ⊢;
      exact ih h1 h2;
    · rcases n1 with ( _ | n1 ) <;> rcases n2 with ( _ | n2 ) <;> simp +decide at h1 h2 ⊢;
      obtain ⟨h, h'⟩ := ih h1 h2; exact ⟨by omega, Bool.not_inj h'⟩

/-! ## KempeCoclosure basic properties -/

/-- Enlarging `P` preserves `KempeCoclosure`. -/
theorem KempeCoclosure.mono {P Q : List Color → Prop} {et : List Color}
    (h : ∀ x, P x → Q x) (hco : KempeCoclosure P et) : KempeCoclosure Q et := by
  intro R hR hRet
  obtain ⟨et', hP, hR'⟩ := hco R hR hRet
  exact ⟨et', h et' hP, hR'⟩

/-- If `P et` holds, then `et` is in its own Kempe coclosure (take et' = et). -/
theorem KempeCoclosure.self {P : List Color → Prop} {et : List Color}
    (hP : P et) : KempeCoclosure P et :=
  fun _ _ hRet => ⟨et, hP, hRet⟩

/-- The empty predicate is vacuously Kempe-closed. -/
theorem KempeClosed.empty : KempeClosed (fun _ => False) :=
  fun _ hf => absurd hf id

-- TODO: `matchg_balanced` (chromogram.v:131) — relates matchg to sumt and gramBalanced.
-- TODO: `match_etrace` (chromogram.v:160)

/-! ## Chromogram length / gramBalanced simp -/

@[simp] theorem Chromogram.length_nil : ([] : Chromogram).length = 0 := rfl

@[simp] theorem Chromogram.length_cons (s : GramSymbol) (w : Chromogram) :
    (s :: w).length = w.length + 1 := rfl

@[simp] theorem gramBalanced_Gpush (d : Nat) (b0 : Bool) (w : Chromogram) :
    gramBalanced d b0 (GramSymbol.Gpush :: w) = gramBalanced (d + 1) b0 w := rfl

@[simp] theorem gramBalanced_Gskip (d : Nat) (b0 : Bool) (w : Chromogram) :
    gramBalanced d b0 (GramSymbol.Gskip :: w) = gramBalanced d (!b0) w := rfl

@[simp] theorem matchg_nil_nil_nil : matchg [] [] [] = true := rfl

@[simp] theorem matchg_empty_trace_nonempty_w (lb : List Bool) (s : GramSymbol)
    (w : Chromogram) : matchg lb [] (s :: w) = false := by cases lb <;> rfl

@[simp] theorem matchg_nonempty_trace_empty_w (lb : List Bool) (c : Color)
    (et : List Color) : matchg lb (c :: et) [] = false := by cases lb <;> cases c <;> rfl

end FourColor.Chromogram