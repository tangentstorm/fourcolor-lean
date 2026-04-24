/-
Copyright (c) 2006-2018 Microsoft Corporation and Inria (Coq version).
Lean 4 port of the Four Color Theorem formalization.

An elementary formalization of the real plane topology required to state
the Four Color Theorem. Uses only basic topology of ℝ².

In the Coq version, this is parametrized over an abstract real number model.
In Lean/Mathlib, we use the concrete real numbers ℝ from Mathlib.
-/
import Mathlib

set_option maxHeartbeats 400000

open Set Topology

namespace FourColor.RealPlane

/-! ## Points and regions in the real plane -/

/-- A point in the real plane. -/
abbrev Point := ℝ × ℝ

/-- A region is a set of points. -/
abbrev Region := Set Point

/-- A map (in the geographic sense) is a relation on points:
    m z1 z2 means z1 and z2 are in the same region. -/
abbrev Map := Point → Region

/-! ## Elementary set operations -/

/-- Two regions meet if they have a common point. -/
def Meet (r1 r2 : Region) : Prop :=
  (r1 ∩ r2).Nonempty

/-! ## Map properties -/

/-- A plain map is a partial equivalence relation (PER). -/
structure PlainMap (m : Map) : Prop where
  sym : ∀ z1 z2, m z1 z2 → m z2 z1
  trans : ∀ z1 z2, m z1 z2 → m z2 ⊆ m z1

/-- The cover of a map: the set of points that belong to some region. -/
def cover (m : Map) : Region := {z | m z z}

/-- A map m1 is a submap of m2 if each region of m1 is contained in
    a region of m2. -/
def Submap (m1 m2 : Map) : Prop :=
  ∀ z, m1 z ⊆ m2 z

/-- Map m has at most n regions. -/
def AtMostRegions (n : ℕ) (m : Map) : Prop :=
  ∃ f : Fin n → Point, ∀ z, z ∈ cover m → ∃ i, m (f i) z

/-! ## Topological properties -/

/-- A region is open in the usual ℝ² topology. -/
def IsOpenRegion (r : Region) : Prop :=
  IsOpen r

/-- The topological closure of a region. -/
def Closure (r : Region) : Region :=
  closure r

/-- A region is connected. -/
def IsConnected (r : Region) : Prop :=
  IsPreconnected r

/-! ## Simple maps -/

/-- A simple map: plain with open and connected regions. -/
structure SimpleMap (m : Map) : Prop extends PlainMap m where
  map_open : ∀ z, IsOpenRegion (m z)
  map_connected : ∀ z, IsConnected (m z)

/-- A finite simple map: simple with finitely many regions. -/
structure FiniteSimpleMap (m : Map) : Prop extends SimpleMap m where
  finite : ∃ n, AtMostRegions n m

/-- A finite simple map is also a plain map (convenience alias). -/
theorem FiniteSimpleMap.plainMap {m : Map} (h : FiniteSimpleMap m) : PlainMap m :=
  h.toSimpleMap.toPlainMap

/-- Symmetry of a simple map's underlying relation. -/
theorem SimpleMap.sym' {m : Map} (h : SimpleMap m) : ∀ z1 z2, m z1 z2 → m z2 z1 :=
  h.toPlainMap.sym

/-- Transitivity of a simple map's underlying relation. -/
theorem SimpleMap.trans' {m : Map} (h : SimpleMap m) : ∀ z1 z2, m z1 z2 → m z2 ⊆ m z1 :=
  h.toPlainMap.trans

/-! ## Intervals and rectangles (realplane.v:80–82) -/

/-- An open interval in ℝ, given by its endpoints. -/
structure Interval where
  lo : ℝ
  hi : ℝ

/-- An open rectangle in the real plane. -/
structure Rectangle where
  hspan : Interval
  vspan : Interval

/-- Membership in an open interval: lo < t < hi. -/
def Interval.contains (s : Interval) (t : ℝ) : Prop :=
  s.lo < t ∧ t < s.hi

/-- The region of points inside a rectangle. -/
def Rectangle.region (rr : Rectangle) : Region :=
  fun z => rr.hspan.contains z.1 ∧ rr.vspan.contains z.2

/-! ## PlainMap transitivity helpers (finitize.v:93–99) -/

/-- If m z1 z2, then (m z1 z) ↔ (m z2 z) for any z. -/
theorem PlainMap.map_transl {m : Map} (mP : PlainMap m) {z1 z2 : Point}
    (h : m z1 z2) : ∀ z, m z1 z ↔ m z2 z := by
  intro z
  constructor
  · intro h1
    exact mP.trans z2 z1 (mP.sym z1 z2 h) h1
  · intro h2
    exact mP.trans z1 z2 h h2

/-- If m z1 z2, then (m z z1) ↔ (m z z2). -/
theorem PlainMap.map_transr {m : Map} (mP : PlainMap m) {z1 z2 : Point}
    (h : m z1 z2) : ∀ z, m z z1 ↔ m z z2 := by
  intro z
  constructor
  · intro h1
    exact mP.sym z2 z (mP.trans z2 z1 (mP.sym z1 z2 h) (mP.sym z z1 h1))
  · intro h2
    exact mP.sym z1 z (mP.trans z1 z2 h (mP.sym z z2 h2))

/-- If m z1 z2, both z1 and z2 are in cover m. -/
theorem PlainMap.map_cover {m : Map} (mP : PlainMap m) {z1 z2 : Point}
    (h : m z1 z2) : cover m z1 ∧ cover m z2 := by
  constructor
  · exact mP.trans z1 z2 h (mP.sym z1 z2 h)
  · exact mP.trans z2 z1 (mP.sym z1 z2 h) h

/-- If two points are related, the first is in the cover. -/
theorem cover_of_rel {m : Map} (hP : PlainMap m) {z1 z2 : Point}
    (h : m z1 z2) : z1 ∈ cover m :=
  (PlainMap.map_cover hP h).1

/-! ## Borders and adjacency -/

/-- The border between the regions of z1 and z2. -/
def border (m : Map) (z1 z2 : Point) : Region :=
  Closure (m z1) ∩ Closure (m z2)

/-- The corner map at point z. -/
def cornerMap (m : Map) (z : Point) : Map :=
  fun z1 z2 => m z1 z2 ∧ z ∈ Closure (m z1)

/-- z is a non-corner point: at most 2 regions of m touch z. -/
def notCorner (m : Map) : Region :=
  {z | AtMostRegions 2 (cornerMap m z)}

/-- Two points are in adjacent regions: they're in different regions and
    their common border contains a non-corner point. -/
def Adjacent (m : Map) (z1 z2 : Point) : Prop :=
  ¬ m z1 z2 ∧ Meet (notCorner m) (border m z1 z2)

/-! ## Coloring -/

/-- A coloring of map m by color map k: k is a plain map that covers m,
    refines m, and gives different colors to adjacent regions. -/
structure MapColoring (m k : Map) : Prop where
  plain : PlainMap k
  cover_sub : cover k ⊆ cover m
  consistent : Submap m k
  adjacent_distinct : ∀ z1 z2, Adjacent m z1 z2 → ¬ k z1 z2

/-- Map m is colorable with at most n colors. -/
def ColorableWith (n : ℕ) (m : Map) : Prop :=
  ∃ k, MapColoring m k ∧ AtMostRegions n k

end FourColor.RealPlane
