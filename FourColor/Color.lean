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

theorem addc_double (c : Color) : c + c + c = c := by
  rw [addc_self, add_Color0_left]

theorem addc_self_add (a b : Color) : a + a + b = b := by
  rw [addc_self, add_Color0_left]

theorem add_addc_self (a b : Color) : a + (b + b) = a := by
  rw [addc_self, add_Color0_right]

theorem addc_left_cancel (c : Color) : Function.Injective (c + ·) := by
  intro a b h
  cases c <;> cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem addc_right_cancel (c : Color) : Function.Injective (· + c) := by
  intro a b h
  cases a <;> cases b <;> cases c <;> first | rfl | exact absurd h (by decide)

/-- Left-commutativity of color addition. -/
theorem addc_left_comm (a b c : Color) : a + (b + c) = b + (a + c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Right-commutativity of color addition. -/
theorem addc_right_comm (a b c : Color) : (a + b) + c = (a + c) + b := by
  cases a <;> cases b <;> cases c <;> rfl

@[simp] theorem add_eq_self_left (c d : Color) : c + d = c ↔ d = Color0 := by
  constructor
  · intro h
    have : c + d = c + Color0 := by rw [h, add_Color0_right]
    exact addc_left_cancel c this
  · rintro rfl
    exact add_Color0_right c

@[simp] theorem add_eq_self_right (c d : Color) : d + c = c ↔ d = Color0 := by
  constructor
  · intro h
    have : d + c = Color0 + c := by rw [h, add_Color0_left]
    exact addc_right_cancel c this
  · rintro rfl
    exact add_Color0_left c

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

-- Alias: in a group where addition is XOR, subtraction equals addition.
theorem apply_sub (g : EdgePerm) (a b : Color) :
    g.apply (a + b) = g.apply a + g.apply b := apply_add g a b

@[simp] theorem inv_apply_inv (g : EdgePerm) (c : Color) :
    g.inv.apply (g.apply c) = c := apply_inv g c

@[simp] theorem apply_inv_apply (g : EdgePerm) (c : Color) :
    g.apply (g.inv.apply c) = c := inv_apply g c

theorem addc_three (a b c : Color) : a + b + c = a + (b + c) := (addc_assoc a b c).symm

-- Coq: color.v:175
theorem apply_zero (g : EdgePerm) : g.apply Color0 = Color0 := by cases g <;> rfl

/-- The identity permutation `Eperm123` acts as the identity on colors. -/
theorem apply_id (c : Color) : Eperm123.apply c = c := rfl

end EdgePerm

/-! ## Trace lemmas (Coq: color.v:217-243) -/

-- Coq: color.v:217
@[simp] theorem trace_nil : trace ([] : List Color) = [] := rfl

theorem trace_nil_eq_nil : trace ([] : List Color) = [] := rfl

-- Coq: color.v:237
theorem length_trace : ∀ s : List Color, (trace s).length = s.length
  | [] => rfl
  | x :: rest => by simp [trace, List.length_zipWith]

@[simp] theorem trace_length (s : List Color) : (trace s).length = s.length := length_trace s

-- Coq: color.v:220
/-- Note: `trace [c] = [c + c] = [Color0]` because the shifted list wraps around. -/
theorem trace_singleton (c : Color) : trace [c] = [c + c] := by
  unfold trace; rfl

theorem sumt_nil : sumt ([] : List Color) = Color0 := rfl

-- Coq: color.v:222
theorem sumt_cons (c : Color) (cs : List Color) :
    sumt (c :: cs) = c + sumt cs := rfl

@[simp] theorem sumt_singleton (c : Color) : sumt [c] = c := by
  rw [sumt_cons, sumt_nil, add_Color0_right]

@[simp] theorem sumt_append (s t : List Color) : sumt (s ++ t) = sumt s + sumt t := by
  induction s with
  | nil => rw [List.nil_append, sumt_nil, add_Color0_left]
  | cons x xs ih => rw [List.cons_append, sumt_cons, sumt_cons, ih, addc_assoc]

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

@[simp] theorem head_color_singleton (c : Color) : head_color [c] = c := rfl

/-! ## Trace permutation (Coq: color.v:234) -/

/-- Apply an edge permutation pointwise to a color sequence. -/
def permt (g : EdgePerm) (s : List Color) : List Color :=
  s.map g.apply

@[simp] theorem permt_nil (g : EdgePerm) : permt g [] = [] := rfl

@[simp] theorem permt_cons (g : EdgePerm) (c : Color) (s : List Color) :
    permt g (c :: s) = g.apply c :: permt g s := rfl

/-- Applying the identity permutation `Eperm123` to a list is the identity. -/
@[simp] theorem permt_id (s : List Color) : permt EdgePerm.Eperm123 s = s := by
  unfold permt
  have : EdgePerm.Eperm123.apply = id := funext (fun c => EdgePerm.apply_id c)
  rw [this, List.map_id]

theorem length_permt (g : EdgePerm) (s : List Color) :
    (permt g s).length = s.length := by simp [permt]

@[simp] theorem permt_length (g : EdgePerm) (s : List Color) :
    (permt g s).length = s.length := length_permt g s

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

@[simp] theorem pairmap_nil (f : Color → Color → Color) (a : Color) :
    pairmap f a [] = [] := rfl

/-- The unrolled trace: pairmap of addition starting from the last element. -/
def urtrace (s : List Color) : List Color :=
  pairmap (· + ·) (s.getLastD Color0) s

@[simp] theorem urtrace_nil : urtrace ([] : List Color) = [] := rfl

/-- Note: `urtrace [c] = [c + c] = [Color0]` because the last element equals `c`,
    so `pairmap` computes `c + c`. -/
theorem urtrace_singleton (c : Color) : urtrace [c] = [c + c] := by
  unfold urtrace; rfl

/-- `urtrace` of a 2-element list is the pair sums in cyclic shift. -/
theorem urtrace_pair (c d : Color) : urtrace [c, d] = [d + c, c + d] := rfl

theorem length_pairmap (f : Color → Color → Color) (a : Color) (s : List Color) :
    (pairmap f a s).length = s.length := by
  induction s generalizing a with
  | nil => rfl
  | cons x xs ih => simp [pairmap, ih]

theorem length_urtrace (s : List Color) :
    (urtrace s).length = s.length := length_pairmap _ _ _

@[simp] theorem urtrace_length (s : List Color) :
    (urtrace s).length = s.length := length_urtrace s

/-- urtrace pairs preserve list nonemptiness. -/
@[simp] theorem urtrace_eq_nil_iff (s : List Color) :
    urtrace s = [] ↔ s = [] := by
  cases s with
  | nil => simp [urtrace_nil]
  | cons c rest =>
    constructor
    · intro h
      have hlen := length_urtrace (c :: rest)
      rw [h, List.length_nil] at hlen
      exact absurd hlen (by simp [List.length_cons])
    · intro h
      exact absurd h (List.cons_ne_nil c rest)

@[simp] theorem urtrace_length_pos (s : List Color) :
    0 < (urtrace s).length ↔ s ≠ [] := by
  rw [urtrace_length, List.length_pos_iff_ne_nil]

@[simp] theorem urtrace_ne_nil_iff (s : List Color) :
    urtrace s ≠ [] ↔ s ≠ [] := by
  simp [urtrace_eq_nil_iff]

/-! ## Clarity helpers -/

@[simp] theorem addc_zero_iff (c : Color) : c + Color0 = Color0 ↔ c = Color0 := by
  constructor
  · intro h; cases c <;> first | rfl | exact absurd h (by decide)
  · rintro rfl; rfl

@[simp] theorem zero_addc_iff (c : Color) : Color0 + c = Color0 ↔ c = Color0 := by
  rw [addc_comm, addc_zero_iff]

theorem addc_ne_zero_of_ne {c d : Color} (h : c ≠ d) : c + d ≠ Color0 := by
  intro hzero; exact h ((add_eq_zero c d).mp hzero)

theorem sumt_cons_zero (c : Color) (cs : List Color) :
    sumt (c :: cs) = Color0 ↔ sumt cs = c := by
  simp only [sumt_cons, add_eq_zero]
  exact eq_comm

/-! ## EdgePerm operation lemmas -/

namespace EdgePerm

@[simp] theorem Eperm123_apply (c : Color) : Eperm123.apply c = c := rfl

@[simp] theorem inv_Eperm123 : Eperm123.inv = Eperm123 := rfl
@[simp] theorem inv_Eperm132 : Eperm132.inv = Eperm132 := rfl
@[simp] theorem inv_Eperm213 : Eperm213.inv = Eperm213 := rfl
@[simp] theorem inv_Eperm321 : Eperm321.inv = Eperm321 := rfl
@[simp] theorem inv_Eperm231 : Eperm231.inv = Eperm312 := rfl
@[simp] theorem inv_Eperm312 : Eperm312.inv = Eperm231 := rfl

theorem apply_zero_eq_zero (g : EdgePerm) : g.apply Color0 = Color0 := apply_zero g

end EdgePerm

/-! ## cbit / ccons simp lemmas -/

@[simp] theorem cbit0_Color0 : cbit0 Color0 = false := rfl
@[simp] theorem cbit0_Color1 : cbit0 Color1 = true := rfl
@[simp] theorem cbit0_Color2 : cbit0 Color2 = false := rfl
@[simp] theorem cbit0_Color3 : cbit0 Color3 = true := rfl

@[simp] theorem cbit1_Color0 : cbit1 Color0 = false := rfl
@[simp] theorem cbit1_Color1 : cbit1 Color1 = false := rfl
@[simp] theorem cbit1_Color2 : cbit1 Color2 = true := rfl
@[simp] theorem cbit1_Color3 : cbit1 Color3 = true := rfl

@[simp] theorem ccons_false_false : ccons false false = Color0 := rfl
@[simp] theorem ccons_false_true : ccons false true = Color1 := rfl
@[simp] theorem ccons_true_false : ccons true false = Color2 := rfl
@[simp] theorem ccons_true_true : ccons true true = Color3 := rfl

/-! ## proper_trace + permt_append/reverse -/

@[simp] theorem proper_trace_nil : ¬ proper_trace [] := by
  unfold proper_trace head_color; simp

theorem proper_trace_cons (c : Color) (s : List Color) :
    proper_trace (c :: s) ↔ c ≠ Color0 := by
  unfold proper_trace head_color; exact Iff.rfl

@[simp] theorem proper_trace_singleton (c : Color) : proper_trace [c] ↔ c ≠ Color0 :=
  proper_trace_cons c []

@[simp] theorem proper_trace_def (et : List Color) :
    proper_trace et ↔ head_color et ≠ Color0 := Iff.rfl

theorem not_proper_trace_iff (et : List Color) :
    ¬ proper_trace et ↔ head_color et = Color0 := by
  unfold proper_trace
  exact not_ne_iff

@[simp] theorem permt_append (g : EdgePerm) (s t : List Color) :
    permt g (s ++ t) = permt g s ++ permt g t := by
  simp [permt, List.map_append]

@[simp] theorem permt_reverse (g : EdgePerm) (s : List Color) :
    permt g s.reverse = (permt g s).reverse := by
  simp [permt, List.map_reverse]

@[simp] theorem permt_inv_apply (g : EdgePerm) (s : List Color) :
    permt g.inv (permt g s) = s := by
  induction s with
  | nil => rfl
  | cons c rest ih => simp only [permt_cons, EdgePerm.apply_inv, ih]

/-- Applying `permt g.inv` to `g.apply c :: permt g s` recovers `c :: s`. -/
theorem permt_apply_then_inv (g : EdgePerm) (c : Color) (s : List Color) :
    permt g.inv (g.apply c :: permt g s) = c :: s := by
  rw [permt_cons, EdgePerm.apply_inv, permt_inv_apply]

@[simp] theorem permt_apply_inv (g : EdgePerm) (s : List Color) :
    permt g (permt g.inv s) = s := by
  induction s with
  | nil => rfl
  | cons c rest ih => simp only [permt_cons, EdgePerm.inv_apply, ih]

/-! ## Compositional helpers for trace operations -/

namespace EdgePerm

theorem apply_inj (g : EdgePerm) {a b : Color} : g.apply a = g.apply b ↔ a = b := by
  constructor
  · exact fun h => g.apply_injective h
  · rintro rfl; rfl

end EdgePerm

theorem permt_singleton (g : EdgePerm) (c : Color) : permt g [c] = [g.apply c] := rfl

/-- `permt g [c1, c2]` distributes via `permt_cons`. -/
theorem permt_pair (g : EdgePerm) (c1 c2 : Color) :
    permt g [c1, c2] = [g.apply c1, g.apply c2] := by
  rw [permt_cons, permt_cons, permt_nil]

/-- `permt` preserves nonemptiness. -/
theorem permt_ne_nil_iff (g : EdgePerm) (s : List Color) :
    permt g s ≠ [] ↔ s ≠ [] := by
  cases s with
  | nil => simp [permt_nil]
  | cons c rest => simp [permt_cons]

theorem sumt_permt (g : EdgePerm) (s : List Color) :
    sumt (permt g s) = g.apply (sumt s) := by
  induction s with
  | nil => simp [sumt, permt, EdgePerm.apply_zero]
  | cons c s ih =>
      change g.apply c + sumt (permt g s) = g.apply (c + sumt s)
      rw [ih, EdgePerm.apply_add]

theorem ctrace_nil : ctrace ([] : List Color) = [Color0] := by rfl

@[simp] theorem ctrace_length (s : List Color) : (ctrace s).length = s.length + 1 := by
  unfold ctrace; simp [List.length_append]

@[simp] theorem sumt_reverse (s : List Color) : sumt s.reverse = sumt s := by
  induction s with
  | nil => rfl
  | cons c cs ih =>
    rw [List.reverse_cons, sumt_append, ih, sumt_singleton, sumt_cons,
        addc_comm c (sumt cs)]

@[simp] theorem sumt_replicate_zero (c : Color) : sumt (List.replicate 0 c) = Color0 := rfl

theorem sumt_replicate_two (c : Color) : sumt (List.replicate 2 c) = Color0 := by
  show c + (c + Color0) = Color0
  simp

theorem head_color_append_left (c : Color) (s t : List Color) :
    head_color ((c :: s) ++ t) = c := rfl

/-- `sumt` over a list equals folding addition from the right with `Color0` as initial value. -/
theorem sumt_eq_foldr (cs : List Color) :
    sumt cs = cs.foldr (· + ·) Color0 := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [sumt_cons, List.foldr_cons, ih]

end Color
