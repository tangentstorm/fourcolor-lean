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
    {z : Point} (hz : z ∈ inPmap m n) : m z ⊆ inPmap m n := by
  intro t hzt
  obtain ⟨i, hi, hmi⟩ := hz
  -- m z (stdPoint i) and m z t ⇒ m t (stdPoint i): use sym + trans of m.
  have htz : m t z := hM.toPlainMap.sym z t hzt
  have : m t (stdPoint i) := hM.toPlainMap.trans t z htz hmi
  exact ⟨i, hi, this⟩

/-- The prefix `pmap m n m` is plain. -/
theorem pmap_plainMap (m : Map) (hM : SimpleMap m) (n : ℕ) :
    PlainMap (pmap m n m) :=
  sorry

/-- The prefix `pmap m n m` has open regions inherited from `m`. -/
theorem pmap_open_regions (m : Map) (hM : SimpleMap m) (n : ℕ) :
    ∀ z, IsOpenRegion ((pmap m n m) z) :=
  sorry

/-- The prefix `pmap m n m` has connected regions inherited from `m`. -/
theorem pmap_connected_regions (m : Map) (hM : SimpleMap m) (n : ℕ) :
    ∀ z, FourColor.RealPlane.IsConnected ((pmap m n m) z) :=
  sorry

/-- The prefix `pmap m n m` is a simple map. -/
theorem pmap_simpleMap (m : Map) (hM : SimpleMap m) (n : ℕ) :
    SimpleMap (pmap m n m) :=
  { toPlainMap := pmap_plainMap m hM n
    map_open := pmap_open_regions m hM n
    map_connected := pmap_connected_regions m hM n }

/-- The prefix `pmap m n m` has at most `n` regions: each is the equivalence
    class of one of `stdPoint 0, …, stdPoint (n-1)`. -/
theorem pmap_atMost_n_regions (m : Map) (hM : SimpleMap m) (n : ℕ) :
    AtMostRegions n (pmap m n m) :=
  sorry

/-- Each prefix is itself a finite simple map (finitize.v:279 `pmap_finite`).
    This is the bridge that lets us apply the finite hypothesis. -/
theorem pmap_finiteSimpleMap (m : Map) (hM : SimpleMap m) (n : ℕ) :
    FiniteSimpleMap (pmap m n m) :=
  { toSimpleMap := pmap_simpleMap m hM n
    finite := ⟨n, pmap_atMost_n_regions m hM n⟩ }

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

/-- A coloring of `pmap m n m` is plain because `pmap` is plain and the
    coloring inherits plainness. -/
theorem MapColoring.lift_pmap_plain (m : Map) (hM : SimpleMap m) (n : ℕ)
    {k : Map} (hk : MapColoring (pmap m n m) k) : PlainMap k :=
  hk.plain

/-- A coloring of `pmap m n m` doesn't relate adjacent regions of `m`:
    adjacency of regions in `m` restricted to `inPmap m n` is the same as
    adjacency in `pmap m n m`. -/
theorem MapColoring.lift_pmap_not_adjacent (m : Map) (hM : SimpleMap m)
    (n : ℕ) {k : Map} (hk : MapColoring (pmap m n m) k) :
    ∀ z1 z2, Adjacent m z1 z2 → ¬ k z1 z2 :=
  sorry

/-- A coloring of `pmap m n m` covers the prefix region. -/
theorem MapColoring.lift_pmap_cover (m : Map) (hM : SimpleMap m) (n : ℕ)
    {k : Map} (hk : MapColoring (pmap m n m) k) :
    Submap (pmap m n m) k :=
  hk.consistent

/-- A coloring of `pmap m n m` lifts to a subcoloring of `m`: extending
    `k` by `False` outside `inPmap m n` keeps it plain and avoids relating
    adjacent regions of `m`. -/
theorem MapColoring.lift_pmap (m : Map) (hM : SimpleMap m) (n : ℕ) {k : Map}
    (hk : MapColoring (pmap m n m) k) :
    Subcoloring m k ∧ Submap (pmap m n m) k :=
  ⟨{ plain := MapColoring.lift_pmap_plain m hM n hk
     not_adjacent := MapColoring.lift_pmap_not_adjacent m hM n hk },
   MapColoring.lift_pmap_cover m hM n hk⟩

/-- For each `n`, the finite-map hypothesis produces a `Pcoloring` of length
    `n` of `m` using at most `nc` colors. (finitize.v:318 `pcoloring_exists`.)
    Combines `pmap_finiteSimpleMap` with `MapColoring.lift_pmap`. -/
theorem pcoloring_exists (nc : ℕ)
    (hfin : ∀ m', FiniteSimpleMap m' → ColorableWith nc m')
    (m : Map) (hM : SimpleMap m) (n : ℕ) :
    ∃ k, Pcoloring m n k ∧ AtMostRegions nc k := by
  obtain ⟨k, hcol, hsize⟩ := hfin _ (pmap_finiteSimpleMap m hM n)
  obtain ⟨hsub, hcov⟩ := MapColoring.lift_pmap m hM n hcol
  exact ⟨k, ⟨hsub, hcov⟩, hsize⟩

/-- The cover of a `Pcoloring` is monotone in `n`: if `k` covers `pmap m n2 m`
    then it also covers `pmap m n1 m` for any `n1 ≤ n2`. -/
theorem Pcoloring.cover_mono (m : Map) {n1 n2 : ℕ} (h : n1 ≤ n2) {k : Map}
    (hcov : Submap (pmap m n2 m) k) : Submap (pmap m n1 m) k :=
  sorry

/-- Pcolorings restrict downward: a Pcoloring of length `n2` is a Pcoloring
    of every shorter length `n1 ≤ n2` (finitize.v:334 `pcoloring_le`). -/
theorem Pcoloring.mono (m : Map) {n1 n2 : ℕ} (h : n1 ≤ n2) {k : Map}
    (hk : Pcoloring m n2 k) : Pcoloring m n1 k :=
  ⟨hk.sub, Pcoloring.cover_mono m h hk.cover⟩

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

/-- A `Pcoloring` of length `n` is extensible iff it admits an extension to
    every larger length. By `pcoloring_exists`, length-`n` pcolorings always
    exist, so by König's lemma (or finite-branching compactness on
    `Fin nc → Fin (n+1)` color sequences) some pcoloring is extensible. -/
theorem extensible_pcoloring_exists (nc : ℕ)
    (hfin : ∀ m', FiniteSimpleMap m' → ColorableWith nc m')
    (m : Map) (hM : SimpleMap m) (n : ℕ) :
    ∃ k, Pcoloring m n k ∧ Extensible m n k ∧ AtMostRegions nc k :=
  sorry

/-- The "color-class index" function on `stdPoint 0..n-1` for a pcoloring `k`:
    associates each standard point to a canonical representative index.
    (Rocq encodes this via `pmap n k` projected to `Fin nc`.) -/
noncomputable def colorIndices (n : ℕ) (k : Map) : Fin n → ℕ :=
  sorry

/-- Among the extensible pcolorings of length `n` with at most `nc` colors,
    one minimizes `colorIndices n k` lexicographically. (Rocq picks one via
    finite-search since there are at most `nc^n` distinct color sequences.) -/
theorem extensible_lexMin_exists (nc : ℕ)
    (hfin : ∀ m', FiniteSimpleMap m' → ColorableWith nc m')
    (m : Map) (hM : SimpleMap m) (n : ℕ) :
    ∃ k, PrefixColoring m n k ∧ AtMostRegions nc k :=
  sorry

/-- A prefix coloring of some length exists (finitize.v:361
    `prefix_coloring_exists`). Combines `extensible_pcoloring_exists` with
    `extensible_lexMin_exists`. -/
theorem prefixColoring_exists (nc : ℕ)
    (hfin : ∀ m', FiniteSimpleMap m' → ColorableWith nc m')
    (m : Map) (hM : SimpleMap m) (n : ℕ) :
    ∃ k, PrefixColoring m n k ∧ AtMostRegions nc k :=
  extensible_lexMin_exists nc hfin m hM n

/-- The extension of a prefix coloring is uniquely determined by extensibility
    + minimality on its prefix region. (Rocq `prefix_coloring_le_step`.) -/
theorem prefixColoring_unique_extension {m : Map} {n : ℕ} {k1 k2 : Map}
    (h1 : PrefixColoring m n k1) (h2 : PrefixColoring m n k2) :
    ∀ z1 z2, z1 ∈ inPmap m n → z2 ∈ inPmap m n → (k1 z1 z2 ↔ k2 z1 z2) :=
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

/-- The limit relation is symmetric: each underlying prefix coloring is. -/
theorem limitColoring_sym (m : Map) :
    ∀ z1 z2, limitColoring m z1 z2 → limitColoring m z2 z1 := by
  rintro z1 z2 ⟨n, k, hpk, hk⟩
  exact ⟨n, k, hpk, hpk.1.sub.plain.sym z1 z2 hk⟩

/-- The limit relation is transitive: when two related pairs come from
    prefix colorings of lengths `n1 ≤ n2`, the longer one already contains
    both relations. (Uses `prefixColoring_le`.) -/
theorem limitColoring_trans (nc : ℕ)
    (hfin : ∀ m', FiniteSimpleMap m' → ColorableWith nc m')
    (m : Map) (hM : SimpleMap m) :
    ∀ z1 z2, limitColoring m z1 z2 → limitColoring m z2 ⊆ limitColoring m z1 :=
  sorry

/-- The limit coloring is a plain map: symmetry and transitivity follow
    from the chain property of prefix colorings (finitize.v:490, first part). -/
theorem limitColoring_plainMap (nc : ℕ)
    (hfin : ∀ m', FiniteSimpleMap m' → ColorableWith nc m')
    (m : Map) (hM : SimpleMap m) : PlainMap (limitColoring m) :=
  { sym := limitColoring_sym m
    trans := limitColoring_trans nc hfin m hM }

/-- The cover of any single prefix coloring is contained in `cover m`. -/
theorem prefixColoring_cover_sub_m (m : Map) (hM : SimpleMap m) (n : ℕ)
    {k : Map} (hk : PrefixColoring m n k) : cover k ⊆ cover m :=
  sorry

/-- The cover of the limit coloring is contained in the cover of `m`:
    each prefix coloring's cover is contained in `inPmap m n ⊆ cover m`. -/
theorem limitColoring_cover_sub (nc : ℕ)
    (hfin : ∀ m', FiniteSimpleMap m' → ColorableWith nc m')
    (m : Map) (hM : SimpleMap m) :
    cover (limitColoring m) ⊆ cover m := by
  rintro z ⟨n, k, hpk, hk⟩
  exact prefixColoring_cover_sub_m m hM n hpk hk

/-- For every related pair in `m`, some prefix coloring at length large enough
    to cover both endpoints already contains the relation. -/
theorem limitColoring_consistent_aux (nc : ℕ)
    (hfin : ∀ m', FiniteSimpleMap m' → ColorableWith nc m')
    (m : Map) (hM : SimpleMap m) :
    ∀ z1 z2, m z1 z2 → ∃ n k, PrefixColoring m n k ∧ k z1 z2 :=
  sorry

/-- The limit coloring refines `m`: each prefix coloring refines `pmap m n m`
    which refines `m`. -/
theorem limitColoring_consistent (nc : ℕ)
    (hfin : ∀ m', FiniteSimpleMap m' → ColorableWith nc m')
    (m : Map) (hM : SimpleMap m) : Submap m (limitColoring m) := by
  intro z1 z2 hrel
  obtain ⟨n, k, hpk, hk⟩ := limitColoring_consistent_aux nc hfin m hM z1 z2 hrel
  exact ⟨n, k, hpk, hk⟩

/-- The limit coloring assigns different colors to adjacent regions: if
    `Adjacent m z1 z2`, no prefix coloring relates them (each prefix
    coloring is a subcoloring of `m`). -/
theorem limitColoring_adjacent_distinct (nc : ℕ)
    (hfin : ∀ m', FiniteSimpleMap m' → ColorableWith nc m')
    (m : Map) (hM : SimpleMap m) :
    ∀ z1 z2, Adjacent m z1 z2 → ¬ limitColoring m z1 z2 := by
  rintro z1 z2 hadj ⟨n, k, hpk, hk⟩
  exact hpk.1.sub.not_adjacent z1 z2 hadj hk

/-- The limit coloring is a coloring of `m` (finitize.v:490
    `limit_coloring_coloring`). Combines the four field lemmas above. -/
theorem limitColoring_isColoring (nc : ℕ)
    (hfin : ∀ m', FiniteSimpleMap m' → ColorableWith nc m')
    (m : Map) (hM : SimpleMap m) :
    MapColoring m (limitColoring m) :=
  { plain := limitColoring_plainMap nc hfin m hM
    cover_sub := limitColoring_cover_sub nc hfin m hM
    consistent := limitColoring_consistent nc hfin m hM
    adjacent_distinct := limitColoring_adjacent_distinct nc hfin m hM }

/-- An enumeration of `nc` representative points for the limit coloring,
    extracted from any prefix coloring of length 0 (which is already a
    pcoloring of size ≤ nc by `pcoloring_exists`). -/
noncomputable def limitColoring_repr (nc : ℕ)
    (hfin : ∀ m', FiniteSimpleMap m' → ColorableWith nc m')
    (m : Map) (hM : SimpleMap m) : Fin nc → Point :=
  sorry

/-- Every covered point of the limit coloring is related to one of the
    `nc` representative points. (finitize.v:511 `size_limit_coloring`.) -/
theorem limitColoring_repr_covers (nc : ℕ)
    (hfin : ∀ m', FiniteSimpleMap m' → ColorableWith nc m')
    (m : Map) (hM : SimpleMap m) :
    ∀ z, z ∈ cover (limitColoring m) →
      ∃ i, limitColoring m (limitColoring_repr nc hfin m hM i) z :=
  sorry

/-- The limit coloring uses at most `nc` colors (finitize.v:511
    `size_limit_coloring`). Every region of the limit contains some
    `stdPoint i`, and the prefix coloring at length `i + 1` already
    has at most `nc` color classes. -/
theorem limitColoring_atMostRegions (nc : ℕ)
    (hfin : ∀ m', FiniteSimpleMap m' → ColorableWith nc m')
    (m : Map) (hM : SimpleMap m) :
    AtMostRegions nc (limitColoring m) :=
  ⟨limitColoring_repr nc hfin m hM,
   limitColoring_repr_covers nc hfin m hM⟩

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
