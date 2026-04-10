/-
Copyright (c) 2006-2018 Microsoft Corporation and Inria (Coq version).
Lean 4 port of the Four Color Theorem formalization.

Discretization: converting a finite simple map in the real plane into a
finite hypermap whose colorings induce colorings of the original map.

The discrete approximation is constructed in five steps:
1. Enumerate regions and adjacencies, choosing representative border points.
2. Construct disjoint rectangles covering border points.
3. Construct approximations of border rectangles.
4. Construct matte approximations of regions meeting all border rectangles.
5. Construct a hypermap from the mattes using the gridmap construction.
-/
import FourColor.Hypermap
import FourColor.Geometry
import FourColor.Coloring
import FourColor.RealPlane

set_option maxHeartbeats 400000

open FourColor.RealPlane Hypermap

namespace FourColor

/-- The discretization theorem: any finite simple map in the real plane
    can be discretized to a planar bridgeless hypermap G, such that
    any four-coloring of G induces a four-coloring of the original map.

    More precisely, if m is a finite simple map, then there exists a
    hypermap G such that:
    - G is planar and bridgeless
    - FourColorable G implies ColorableWith 4 m -/
theorem discretize_to_hypermap (m : Map)
    (hm : FiniteSimpleMap m) :
    ∃ G : Hypermap, Planar G ∧ Bridgeless G ∧
      (FourColorable G → ColorableWith 4 m) := by
  sorry

end FourColor
