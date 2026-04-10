/-
Copyright (c) 2006-2018 Microsoft Corporation and Inria (Coq version).
Lean 4 port of the Four Color Theorem formalization.

Extension of the Four Color Theorem from finite to arbitrary simple maps
using a compactness argument. We use a special case of the compactness
theorem for predicate logic: since the plane is locally compact and maps
have countably many regions, we can construct a global coloring as the
limit of an ascending chain of finite colorings.

The key idea is to enumerate the regions by scaled grid points, and
define a canonical "prefix coloring" for each finite approximation
that is lexicographically minimal among extensible colorings. The
limit of this chain is the desired global coloring.
-/
import RequestProject.FourColor.RealPlane

set_option maxHeartbeats 400000

open FourColor.RealPlane

namespace FourColor

/-- The compactness extension theorem: if all finite simple maps are
    n-colorable, then all simple maps are n-colorable.

    This bridges the gap between the finite combinatorial result and
    the general topological statement. -/
theorem compactness_extension (n : ℕ)
    (hfin : ∀ m : Map, FiniteSimpleMap m → ColorableWith n m) :
    ∀ m : Map, SimpleMap m → ColorableWith n m := by
  sorry

end FourColor
