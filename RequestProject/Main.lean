/-
The Four Color Theorem
======================
Lean 4 port of the Coq formalization by Georges Gonthier et al.
(Microsoft Research and INRIA, 2006-2018)

Original: https://github.com/coq-community/fourcolor

This is a structured port of the formal proof of the Four Color Theorem,
which states that every map of the plane can be colored with at most four
colors such that no two adjacent regions share the same color.

## Structure

The proof is organized into the following modules:

- `Hypermap`: Core hypermap data structure (finite type with three
  permutations satisfying the triangular identity)
- `Color`: The four colors with XOR arithmetic
- `Geometry`: Geometric properties (bridgeless, plain, cubic, etc.)
- `Coloring`: Map coloring definitions and properties
- `Walkup`: The Walkup construction for removing darts
- `Jordan`: Equivalence of Euler and Jordan planarity
- `Cube`: Reduction to cubic maps
- `Configurations`: The 633 reducible configurations
- `Unavoidability`: The discharge method
- `Combinatorial4ct`: The combinatorial Four Color Theorem
- `RealPlane`: Topological definitions for the real plane
- `Discretize`: Converting plane maps to hypermaps
- `Finitize`: Compactness extension to infinite maps
- `FourColor`: The top-level theorem

## Status

This port captures the mathematical structure of the original Coq proof.
Core definitions are fully ported. Many proofs are left as `sorry` pending
further formalization work, particularly:
- The computational verification of 633 configurations (reducibility)
- The discharge procedure (unavoidability)
- The discretization and compactness arguments
- Various Walkup transform lemmas

The key definitions and theorem statements faithfully mirror the original
Coq formalization.
-/

import RequestProject.FourColor.FourColor
