/-
Copyright (c) 2006-2018 Microsoft Corporation and Inria (Coq version).
Lean 4 port of the Four Color Theorem formalization.

The top-level statement and proof of the Four Color Theorem:
  Every simple map in the real plane is four-colorable.

The proof combines three main ingredients:
1. **Combinatorial 4CT** (`four_color_hypermap`): Every planar bridgeless
   hypermap is four-colorable. This is proved using:
   - The cube construction (reducing to plain cubic maps)
   - Reducibility (all 633 configurations are C-reducible)
   - Unavoidability (every planar map contains a reducible configuration)

2. **Discretization** (`discretize_to_hypermap`): Every finite simple map
   can be discretized to a planar bridgeless hypermap whose colorings
   induce colorings of the original map.

3. **Compactness** (`compactness_extension`): If all finite simple maps
   are n-colorable, then all simple maps are n-colorable.

The final theorem follows by combining these three components.
-/
import RequestProject.FourColor.Hypermap
import RequestProject.FourColor.Geometry
import RequestProject.FourColor.Coloring
import RequestProject.FourColor.Cube
import RequestProject.FourColor.Combinatorial4ct
import RequestProject.FourColor.Discretize
import RequestProject.FourColor.Finitize
import RequestProject.FourColor.RealPlane

set_option maxHeartbeats 400000

open FourColor.RealPlane Hypermap

namespace FourColor

/-! ## The Four Color Theorem -/

/-- The Four Color Theorem for finite simple maps in the real plane:
    every finite simple map is four-colorable. -/
theorem four_color_finite (m : Map) (hm : FiniteSimpleMap m) :
    ColorableWith 4 m := by
  obtain ⟨G, hP, hB, hCol⟩ := discretize_to_hypermap m hm
  exact hCol (four_color_hypermap G hP hB)

/-- **The Four Color Theorem**: every simple map in the real plane
    is four-colorable.

    This is the main result of the formalization. It states that for
    any map of the plane where regions are open connected sets,
    four colors suffice to color all regions such that no two
    adjacent regions receive the same color.

    The proof uses the compactness extension to reduce from arbitrary
    maps to finite maps, then applies the finite case. -/
theorem four_color (m : Map) (hm : SimpleMap m) :
    ColorableWith 4 m := by
  exact compactness_extension 4 four_color_finite m hm

end FourColor
