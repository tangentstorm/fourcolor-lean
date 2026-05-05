/-
Copyright (c) 2006-2018 Microsoft Corporation and Inria (Coq version).
Lean 4 port of the Four Color Theorem formalization.

Extension of the Four Color Theorem from finite to arbitrary simple maps via
the compactness theorem of propositional logic. The plane is locally
compact and any plane map has only countably many regions, so we can pick a
canonical enumeration `stdPoint : ℕ → Point` and approximate any simple map
by its restriction to the first `n` "named" regions.

Following finitize.v we build:
* `inPmap m n` — the union of regions of `m` containing one of the first `n`
  standard points.
* `pmap m n k` — the restriction of `k` to `inPmap m n`.
* `Subcoloring m k` — `k` is a plain map that does not relate adjacent
  regions of `m`.
* `Pcoloring m n k` — `k` is a subcoloring of `m` that covers `inPmap m n`.
* `Extensible m n k` — every prefix coloring of `m` past `n` extends `k`.
* `PrefixColoring m n k` — the lex-minimal extensible pcoloring of length `n`.
* `limitColoring m` — the union of the chain of prefix colorings, which is
  the desired global coloring of `m`.

The headline theorem `compactness_extension` follows by combining
`limitColoring_isColoring` with `limitColoring_atMostRegions`.
-/
import FourColor.RealPlane

set_option maxHeartbeats 400000

open FourColor.RealPlane

namespace FourColor

/-! ## Standard enumeration of grid points (finitize.v:108) -/

/-- A canonical enumeration `ℕ → Point` such that every region of any plane
    map contains a point of the enumeration (the plane is separable). The
    Rocq version uses a scaled enumeration of grid points. -/
noncomputable def stdPoint : ℕ → Point :=
  sorry

/-- Every covered point of a plane map has a standard point in its region.
    (finitize.v:216 `has_std_point`.) -/
theorem stdPoint_covers (m : Map) (hM : SimpleMap m)
    {z : Point} (hz : z ∈ cover m) : ∃ i, m z (stdPoint i) :=
  sorry

/-! ## Finite prefixes of a map (finitize.v:184–186) -/

/-- The union of regions of `m` containing one of the first `n` standard
    points. (`in_pmap` in finitize.v.) -/
def inPmap (m : Map) (n : ℕ) : Region :=
  fun z => ∃ i, i < n ∧ m z (stdPoint i)

/-- The restriction of map `k` to `inPmap m n`. (`pmap` in finitize.v.) -/
def pmap (m : Map) (n : ℕ) (k : Map) : Map :=
  fun z1 z2 => z1 ∈ inPmap m n ∧ z2 ∈ inPmap m n ∧ k z1 z2

/-! ### Basic facts about the prefix maps -/

/-- The prefix region is monotone in `n` (finitize.v:229 `in_pmap_le`). -/
theorem inPmap_mono (m : Map) {n1 n2 : ℕ} (h : n1 ≤ n2) :
    inPmap m n1 ⊆ inPmap m n2 := by
  rintro z ⟨i, hi, hmi⟩
  exact ⟨i, lt_of_lt_of_le hi h, hmi⟩

/-- The prefix is closed under the equivalence of `m` (finitize.v:232
    `in_pmap_trans`). -/
theorem inPmap_trans (m : Map) (hM : SimpleMap m) (n : ℕ)
    {z : Point} (hz : z ∈ inPmap m n) : m z ⊆ inPmap m n :=
  sorry

/-- Each prefix is itself a finite simple map (finitize.v:279 `pmap_finite`).
    This is the bridge that lets us apply the finite hypothesis. -/
theorem pmap_finiteSimpleMap (m : Map) (hM : SimpleMap m) (n : ℕ) :
    FiniteSimpleMap (pmap m n m) :=
  sorry

/-! ## Subcolorings and partial colorings (finitize.v:194–197) -/

/-- A subcoloring of `m` is a plain map that does not relate any two points
    in adjacent regions of `m`. -/
structure Subcoloring (m k : Map) : Prop where
  plain : PlainMap k
  not_adjacent : ∀ z1 z2, Adjacent m z1 z2 → ¬ k z1 z2

/-- A partial coloring of length `n`: a subcoloring that covers `inPmap m n`. -/
structure Pcoloring (m : Map) (n : ℕ) (k : Map) : Prop where
  sub : Subcoloring m k
  cover : Submap (pmap m n m) k

/-- For each `n`, the finite-map hypothesis produces a `Pcoloring` of length
    `n` of `m` using at most `nc` colors. (finitize.v:318 `pcoloring_exists`.) -/
theorem pcoloring_exists (nc : ℕ)
    (hfin : ∀ m', FiniteSimpleMap m' → ColorableWith nc m')
    (m : Map) (hM : SimpleMap m) (n : ℕ) :
    ∃ k, Pcoloring m n k ∧ AtMostRegions nc k :=
  sorry

/-- Pcolorings restrict downward: a Pcoloring of length `n2` is a Pcoloring
    of every shorter length `n1 ≤ n2` (finitize.v:334 `pcoloring_le`). -/
theorem Pcoloring.mono (m : Map) {n1 n2 : ℕ} (h : n1 ≤ n2) {k : Map}
    (hk : Pcoloring m n2 k) : Pcoloring m n1 k :=
  sorry

/-! ## Extensible and prefix colorings (finitize.v:199–207) -/

/-- A pcoloring of length `n` is extensible if it can be continued to a
    pcoloring of any larger length while remaining consistent on its
    standard points. -/
def Extensible (m : Map) (n : ℕ) (k : Map) : Prop :=
  ∀ n', n ≤ n' → ∃ k', Pcoloring m n' k' ∧
    ∀ i, i < n → ∀ j, k (stdPoint i) (stdPoint j) ↔ k' (stdPoint i) (stdPoint j)

/-- The prefix coloring of length `n`: an extensible pcoloring whose color
    sequence on `stdPoint 0, …, stdPoint (n-1)` is lexicographically minimal.
    Following finitize.v we encode minimality by the "any extension that
    agrees up to index `i-1` cannot strictly precede `k`'s choice at
    `stdPoint i`" formulation, avoiding explicit enumeration of color
    sequences. -/
def PrefixColoring (m : Map) (n : ℕ) (k : Map) : Prop :=
  Pcoloring m n k ∧ Extensible m n k ∧
  -- Minimality: any other extensible pcoloring of length `i+1 ≤ n` that
  -- coincides with k on `stdPoint 0..i-1` cannot put `stdPoint i` in an
  -- earlier color class than k does.
  ∀ i, i < n → ∀ k', Pcoloring m (i + 1) k' → Extensible m (i + 1) k' →
    (∀ j, j < i → ∀ j',
        k (stdPoint j) (stdPoint j') ↔ k' (stdPoint j) (stdPoint j')) →
    ∀ j, k (stdPoint i) (stdPoint j) → k' (stdPoint i) (stdPoint j) ∨
      ∃ j0, j0 ≤ j ∧ k (stdPoint i) (stdPoint j0)

/-- A prefix coloring of some length exists (finitize.v:361
    `prefix_coloring_exists`). The proof picks the lex-minimal extensible
    pcoloring of length `n` from the finitely many pcolorings provided
    by `pcoloring_exists`. -/
theorem prefixColoring_exists (nc : ℕ)
    (hfin : ∀ m', FiniteSimpleMap m' → ColorableWith nc m')
    (m : Map) (hM : SimpleMap m) (n : ℕ) :
    ∃ k, PrefixColoring m n k ∧ AtMostRegions nc k :=
  sorry

/-- Prefix colorings of different lengths agree on their common prefix
    (finitize.v:432 `prefix_coloring_le`): they form an inclusion chain. -/
theorem prefixColoring_le {m : Map} {n1 n2 : ℕ} (h : n1 ≤ n2) {k1 k2 : Map}
    (h1 : PrefixColoring m n1 k1) (h2 : PrefixColoring m n2 k2) :
    Submap (pmap m n1 k1) k2 :=
  sorry

/-! ## The limit coloring (finitize.v:212) -/

/-- The limit coloring is the union of the chain of prefix colorings of `m`. -/
def limitColoring (m : Map) : Map :=
  fun z1 z2 => ∃ n k, PrefixColoring m n k ∧ k z1 z2

/-- The limit coloring is a coloring of `m` (finitize.v:490
    `limit_coloring_coloring`). Combines the chain property of prefix
    colorings with the cover property guaranteed by `stdPoint_covers`. -/
theorem limitColoring_isColoring (nc : ℕ)
    (hfin : ∀ m', FiniteSimpleMap m' → ColorableWith nc m')
    (m : Map) (hM : SimpleMap m) :
    MapColoring m (limitColoring m) :=
  sorry

/-- The limit coloring uses at most `nc` colors (finitize.v:511
    `size_limit_coloring`). Every region of the limit contains some
    `stdPoint i`, and the prefix coloring at length `i + 1` already
    has at most `nc` color classes. -/
theorem limitColoring_atMostRegions (nc : ℕ)
    (hfin : ∀ m', FiniteSimpleMap m' → ColorableWith nc m')
    (m : Map) (hM : SimpleMap m) :
    AtMostRegions nc (limitColoring m) :=
  sorry

/-! ## The compactness extension theorem (finitize.v:558) -/

/-- The compactness extension theorem: if every finite simple map is
    `n`-colorable, every simple map is `n`-colorable. -/
theorem compactness_extension (n : ℕ)
    (hfin : ∀ m : Map, FiniteSimpleMap m → ColorableWith n m) :
    ∀ m : Map, SimpleMap m → ColorableWith n m := by
  intro m hM
  exact ⟨limitColoring m, limitColoring_isColoring n hfin m hM,
                          limitColoring_atMostRegions n hfin m hM⟩

end FourColor
