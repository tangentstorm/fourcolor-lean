/-
Copyright (c) 2006-2018 Microsoft Corporation and Inria (Coq version).
Lean 4 port of the Four Color Theorem formalization.

The four colors, with color sum (XOR) and comparison.
-/
import Mathlib

set_option maxHeartbeats 400000

/-! ## The four colors -/

/-- The type of four colors used in map coloring. -/
inductive Color : Type where
  | Color0 : Color
  | Color1 : Color
  | Color2 : Color
  | Color3 : Color
  deriving DecidableEq, Repr

namespace Color

instance : Fintype Color where
  elems := {Color0, Color1, Color2, Color3}
  complete := by intro x; cases x <;> simp

instance : Inhabited Color := ⟨Color0⟩

/-! ## Color addition (bitwise XOR) -/

/-- Bitwise XOR of colors (corresponding to edge coloring traces). -/
def addc : Color → Color → Color
  | Color0, c => c
  | c, Color0 => c
  | Color1, Color1 => Color0
  | Color1, Color2 => Color3
  | Color1, Color3 => Color2
  | Color2, Color1 => Color3
  | Color2, Color2 => Color0
  | Color2, Color3 => Color1
  | Color3, Color1 => Color2
  | Color3, Color2 => Color1
  | Color3, Color3 => Color0

instance : Add Color := ⟨addc⟩

@[simp] theorem add_Color0_left (c : Color) : Color0 + c = c := by cases c <;> rfl
@[simp] theorem add_Color0_right (c : Color) : c + Color0 = c := by cases c <;> rfl

theorem addc_comm (c1 c2 : Color) : c1 + c2 = c2 + c1 := by
  cases c1 <;> cases c2 <;> rfl

theorem addc_assoc (c1 c2 c3 : Color) : c1 + (c2 + c3) = (c1 + c2) + c3 := by
  cases c1 <;> cases c2 <;> cases c3 <;> rfl

@[simp] theorem addc_self (c : Color) : c + c = Color0 := by cases c <;> rfl

theorem addc_left_cancel (c : Color) : Function.Injective (c + ·) := by
  intro a b h
  cases c <;> cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem addc_right_cancel (c : Color) : Function.Injective (· + c) := by
  intro a b h
  cases a <;> cases b <;> cases c <;> first | rfl | exact absurd h (by decide)

/-! ## Color bits -/

/-- The lower bit of a color. -/
def cbit0 : Color → Bool
  | Color0 => false
  | Color1 => true
  | Color2 => false
  | Color3 => true

/-- The higher bit of a color. -/
def cbit1 : Color → Bool
  | Color0 => false
  | Color1 => false
  | Color2 => true
  | Color3 => true

/-- Construct a color from two bits. -/
def ccons : Bool → Bool → Color
  | false, false => Color0
  | false, true  => Color1
  | true,  false => Color2
  | true,  true  => Color3

@[simp] theorem ccons_cbit (c : Color) : ccons (cbit1 c) (cbit0 c) = c := by
  cases c <;> rfl

/-! ## Edge permutations -/

/-- The six permutations of the three nonzero colors. -/
inductive EdgePerm : Type where
  | Eperm123 : EdgePerm  -- identity
  | Eperm132 : EdgePerm  -- swap Color2 and Color3
  | Eperm213 : EdgePerm  -- swap Color1 and Color2
  | Eperm231 : EdgePerm  -- cyclic: 1→2→3→1
  | Eperm312 : EdgePerm  -- cyclic: 1→3→2→1
  | Eperm321 : EdgePerm  -- swap Color1 and Color3
  deriving DecidableEq, Repr

namespace EdgePerm

/-- Apply an edge permutation to a color. -/
def apply : EdgePerm → Color → Color
  | Eperm123, c => c
  | Eperm132, Color0 => Color0
  | Eperm132, Color1 => Color1
  | Eperm132, Color2 => Color3
  | Eperm132, Color3 => Color2
  | Eperm213, Color0 => Color0
  | Eperm213, Color1 => Color2
  | Eperm213, Color2 => Color1
  | Eperm213, Color3 => Color3
  | Eperm231, Color0 => Color0
  | Eperm231, Color1 => Color2
  | Eperm231, Color2 => Color3
  | Eperm231, Color3 => Color1
  | Eperm312, Color0 => Color0
  | Eperm312, Color1 => Color3
  | Eperm312, Color2 => Color1
  | Eperm312, Color3 => Color2
  | Eperm321, Color0 => Color0
  | Eperm321, Color1 => Color3
  | Eperm321, Color2 => Color2
  | Eperm321, Color3 => Color1

instance : CoeFun EdgePerm (fun _ => Color → Color) := ⟨apply⟩

/-- The inverse of an edge permutation. -/
def inv : EdgePerm → EdgePerm
  | Eperm123 => Eperm123
  | Eperm132 => Eperm132
  | Eperm213 => Eperm213
  | Eperm231 => Eperm312
  | Eperm312 => Eperm231
  | Eperm321 => Eperm321

end EdgePerm

/-! ## Traces -/

/-- The trace (edge coloring) of a perimeter coloring sequence.
    trace s[i] = s[i] + s[i+1 mod |s|]. -/
def trace (s : List Color) : List Color :=
  match s with
  | [] => []
  | x :: rest =>
    let shifted := rest ++ [x]
    List.zipWith (· + ·) (x :: rest) shifted

/-- The sum of all colors in a sequence. -/
def sumt : List Color → Color
  | [] => Color0
  | c :: cs => c + sumt cs

/-- The partial trace: trace without the last element. -/
def ptrace (s : List Color) : List Color :=
  (trace s).dropLast

/-! ## Edge-permutation lemmas (Coq: color.v:163-175) -/

namespace EdgePerm

-- Coq: color.v:163
theorem inv_inv : ∀ g : EdgePerm, g.inv.inv = g := by intro g; cases g <;> rfl

-- Coq: color.v:165
theorem apply_inv (g : EdgePerm) (c : Color) : g.inv.apply (g.apply c) = c := by
  cases g <;> cases c <;> rfl

-- Coq: color.v:167
theorem inv_apply (g : EdgePerm) (c : Color) : g.apply (g.inv.apply c) = c := by
  cases g <;> cases c <;> rfl

-- Coq: color.v:169
theorem apply_injective (g : EdgePerm) : Function.Injective g.apply := by
  intro a b h; rw [← apply_inv g a, ← apply_inv g b, h]

-- Coq: color.v:171
theorem apply_add (g : EdgePerm) (c1 c2 : Color) :
    g.apply (c1 + c2) = g.apply c1 + g.apply c2 := by
  cases g <;> cases c1 <;> cases c2 <;> rfl

-- Coq: color.v:175
theorem apply_zero (g : EdgePerm) : g.apply Color0 = Color0 := by cases g <;> rfl

end EdgePerm

/-! ## Trace lemmas (Coq: color.v:217-243) -/

-- Coq: color.v:217
@[simp] theorem trace_nil : trace ([] : List Color) = [] := rfl

-- Coq: color.v:237
theorem length_trace : ∀ s : List Color, (trace s).length = s.length
  | [] => rfl
  | x :: rest => by simp [trace, List.length_zipWith]

-- Coq: color.v:220
theorem sumt_nil : sumt ([] : List Color) = Color0 := rfl

-- Coq: color.v:222
theorem sumt_cons (c : Color) (cs : List Color) :
    sumt (c :: cs) = c + sumt cs := rfl

/-! ## Color addition cancellation (Coq: color.v:99) -/

-- Coq: color.v:99
theorem add_eq_zero (c1 c2 : Color) : c1 + c2 = Color0 ↔ c1 = c2 := by
  constructor
  · intro h; cases c1 <;> cases c2 <;> first | rfl | exact absurd h (by decide)
  · rintro rfl; exact addc_self c1

/-! ## Head color and proper trace (Coq: color.v:220-222) -/

/-- The first color in a sequence, defaulting to Color0. -/
def head_color : List Color → Color
  | []     => Color0
  | c :: _ => c

/-- A trace is proper when its first entry is nonzero. -/
def proper_trace (et : List Color) : Prop := head_color et ≠ Color0

@[simp] theorem head_color_nil : head_color ([] : List Color) = Color0 := rfl

@[simp] theorem head_color_cons (c : Color) (s : List Color) :
    head_color (c :: s) = c := rfl

/-! ## Trace permutation (Coq: color.v:234) -/

/-- Apply an edge permutation pointwise to a color sequence. -/
def permt (g : EdgePerm) (s : List Color) : List Color :=
  s.map g.apply

@[simp] theorem permt_nil (g : EdgePerm) : permt g [] = [] := rfl

@[simp] theorem permt_cons (g : EdgePerm) (c : Color) (s : List Color) :
    permt g (c :: s) = g.apply c :: permt g s := rfl

theorem length_permt (g : EdgePerm) (s : List Color) :
    (permt g s).length = s.length := by simp [permt]

/-! ## Closed trace (Coq: color.v:238) -/

/-- The closed trace: append the sum of the trace to itself. -/
def ctrace (et : List Color) : List Color := et ++ [sumt et]

@[simp] theorem length_ctrace (et : List Color) :
    (ctrace et).length = et.length + 1 := by
  simp [ctrace, List.length_append]

/-! ## Pairmap helper and unrolled trace (Coq: color.v:243) -/

/-- Apply a binary function to consecutive pairs, starting with an initial value.
    `pairmap f a [x₁, x₂, …, xₙ] = [f a x₁, f x₁ x₂, …, f xₙ₋₁ xₙ]` -/
def pairmap (f : Color → Color → Color) : Color → List Color → List Color
  | _, []      => []
  | a, x :: xs => f a x :: pairmap f x xs

/-- The unrolled trace: pairmap of addition starting from the last element. -/
def urtrace (s : List Color) : List Color :=
  pairmap (· + ·) (s.getLastD Color0) s

@[simp] theorem urtrace_nil : urtrace ([] : List Color) = [] := rfl

theorem length_pairmap (f : Color → Color → Color) (a : Color) (s : List Color) :
    (pairmap f a s).length = s.length := by
  induction s generalizing a with
  | nil => rfl
  | cons x xs ih => simp [pairmap, ih]

theorem length_urtrace (s : List Color) :
    (urtrace s).length = s.length := length_pairmap _ _ _

end Color
