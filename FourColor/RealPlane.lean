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
