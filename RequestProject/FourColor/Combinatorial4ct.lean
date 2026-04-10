/-
Copyright (c) 2006-2018 Microsoft Corporation and Inria (Coq version).
Lean 4 port of the Four Color Theorem formalization.

The constructive proof of the Four Color Theorem for finite combinatorial
hypermaps. This combines:
  1. The cube construction (reducing to plain cubic maps)
  2. Strong induction on the number of darts
  3. Unavoidability (no minimal counter-example exists)
  4. Reducibility (all 633 configurations are C-reducible)
-/
import RequestProject.FourColor.Hypermap
import RequestProject.FourColor.Geometry
import RequestProject.FourColor.Coloring
import RequestProject.FourColor.Cube
import RequestProject.FourColor.Configurations
import RequestProject.FourColor.Unavoidability

set_option maxHeartbeats 800000

open Hypermap FourColor

namespace FourColor

/-- Every planar bridgeless plain precubic hypermap (at universe 0) is four-colorable.
    Proved by strong induction on the number of darts, using unavoidability to
    rule out minimal counter-examples. -/
private theorem four_color_plain_precubic (n : ℕ) :
    ∀ G : Hypermap.{0},
      Fintype.card G.Dart = n →
      Planar G → Bridgeless G → Plain G → Precubic G → FourColorable G := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro G hcard hP hB hPl hPc
    by_contra h_not
    -- G is a minimal counter-example
    have hMCE : MinimalCounterExample G :=
      ⟨h_not, hP, hB, hPl, hPc, fun H hlt hPH hBH hPlH hPcH =>
        ih (Fintype.card H.Dart) (hcard ▸ hlt) H rfl hPH hBH hPlH hPcH⟩
    -- But unavoidability says no minimal counter-example exists
    exact unavoidability the_reducibility G hMCE

/-- The Four Color Theorem for finite combinatorial hypermaps:
    every planar bridgeless hypermap is four-colorable.

    Proof sketch (following Gonthier):
    1. By cube_colorable, it suffices to prove FourColorable (cube G).
    2. cube G is planar, bridgeless, plain, and cubic (hence precubic).
    3. By strong induction on #|cube G|:
       - Either cube G is four-colorable (and we're done), or
       - cube G would be a minimal counter-example.
    4. But by unavoidability + reducibility, no minimal counter-example exists.
       Contradiction. -/
theorem four_color_hypermap (G : Hypermap.{0})
    (hP : Planar G) (hB : Bridgeless G) :
    FourColorable G := by
  apply cube_colorable
  exact four_color_plain_precubic _
    (cube G) rfl
    ((planar_cube G).mp hP)
    ((bridgeless_cube G).mp hB)
    (plain_cube G)
    (fun x => (cubic_cube G x).1)

end FourColor
