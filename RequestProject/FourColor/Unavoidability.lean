/-
Copyright (c) 2006-2018 Microsoft Corporation and Inria (Coq version).
Lean 4 port of the Four Color Theorem formalization.

The main unavoidability theorem: assuming all configurations are reducible,
no minimal counter-example exists. This is proved by the discharge method,
showing that every planar map must contain at least one of the 633 reducible
configurations.

The proof proceeds by contradiction: assuming a minimal counter-example exists,
we use the discharge procedure to show that every vertex must be adjacent to
one of the configurations, contradicting the assumption that none of them
can appear (since they are all reducible).
-/
import RequestProject.FourColor.Hypermap
import RequestProject.FourColor.Geometry
import RequestProject.FourColor.Coloring
import RequestProject.FourColor.Configurations

set_option maxHeartbeats 400000

open Hypermap FourColor

namespace FourColor

/-- The unavoidability theorem: if all configurations in theConfigs are
    C-reducible, then no minimal counter-example exists.

    The Coq proof proceeds by examining the dscore (discharge score) of
    each vertex, showing it must be zero by the discharge method, but
    finding a positive one leads to a configuration fit, contradicting
    reducibility.

    The proof handles hub arities 5 through 11, with each case covered
    by a dedicated presentation (present5.v through present11.v). -/
theorem unavoidability :
    Reducibility → ∀ G : Hypermap, ¬ MinimalCounterExample G := by
  sorry

end FourColor
