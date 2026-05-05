/-
Challenge module for the leanprover/comparator tool.

This file states the headline theorems of the port without proof. The
`FourColor` library (referenced as the comparator's `solution_module`) supplies
the actual proofs. The comparator builds both modules in sandboxed Lake
environments, then verifies that every name listed in `theorem_names` of
`config.json` reduces to the same proposition in both, and that the solution
relies only on the axioms permitted by `permitted_axioms`.
-/
import FourColor.RealPlane
import FourColor.Coloring
import FourColor.Hypermap
import FourColor.Geometry

set_option maxHeartbeats 400000

open FourColor.RealPlane Hypermap

namespace FourColor

/-- **Four Color Theorem** (challenge statement): every simple map of the real
    plane is four-colorable. -/
theorem four_color (m : Map) (hm : SimpleMap m) :
    ColorableWith 4 m :=
  sorry

/-- **Four Color Theorem, finite case** (challenge statement): every finite
    simple map is four-colorable. -/
theorem four_color_finite (m : Map) (hm : FiniteSimpleMap m) :
    ColorableWith 4 m :=
  sorry

/-- **Combinatorial Four Color Theorem** (challenge statement): every planar
    bridgeless hypermap is four-colorable. -/
theorem four_color_hypermap (G : Hypermap.{0})
    (_hP : Planar G) (_hB : Bridgeless G) :
    FourColorable G :=
  sorry

end FourColor
