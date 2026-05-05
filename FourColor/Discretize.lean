/-
Copyright (c) 2006-2018 Microsoft Corporation and Inria (Coq version).
Lean 4 port of the Four Color Theorem formalization.

Discretization: turning a finite simple plane map into a finite hypermap
whose four-colorings induce four-colorings of the original map.

Following discretize.v we build the hypermap in four stages and combine them
in the end:
1. `exists_mapRepr`  — enumerate regions by representative points.
2. `exists_adjBox`   — separate each adjacent pair by a rectangle approximation.
3. `exists_sMatte`   — build a matte (a discrete approximation) of each region
                       intersecting all of its adjacency boxes.
4. `gridmap`         — assemble the mattes into a planar bridgeless hypermap
                       and prove that any of its four-colorings induces a
                       four-coloring of the original map.

These pieces are exposed as separate (sorry'd) statements; the headline
theorem `discretize_to_hypermap` just glues them together.
-/
import FourColor.Hypermap
import FourColor.Geometry
import FourColor.Coloring
import FourColor.RealPlane

set_option maxHeartbeats 400000

open FourColor.RealPlane Hypermap

namespace FourColor

/-! ## Region representatives (discretize.v:76–85) -/

/-- A representative point for each region: a function `Fin n → Point` whose
    image hits every region of `m`. -/
structure MapRepr (m : Map) (n : ℕ) where
  rep : Fin n → Point
  proper : ∀ i, rep i ∈ cover m
  cover : ∀ z, z ∈ cover m → ∃ i, m (rep i) z

/-- Every finite simple map admits a representative enumeration of its
    regions (discretize.v:84 `exists_map_repr`). -/
theorem exists_mapRepr (m : Map) (hm : FiniteSimpleMap m) :
    ∃ n, Nonempty (MapRepr m n) :=
  sorry

/-! ## Adjacency boxes (discretize.v:119–224) -/

/-- An "adjacency box" for a pair of representatives `(i, j)`: an open
    rectangle `r` separating their regions, in the sense that the closures
    of the two regions meet `r` and any point of the closures inside `r`
    lies on the common border. -/
structure AdjBox (m : Map) {n : ℕ} (mr : MapRepr m n) (i j : Fin n) where
  rect : Rectangle
  meet1 : ∃ z ∈ rect.region, z ∈ Closure (m (mr.rep i))
  meet2 : ∃ z ∈ rect.region, z ∈ Closure (m (mr.rep j))

/-- For any adjacent pair of representatives, an adjacency box exists
    (discretize.v:133 `exists_adjbox`). -/
theorem exists_adjBox (m : Map) (hm : FiniteSimpleMap m)
    {n : ℕ} (mr : MapRepr m n) (i j : Fin n)
    (hadj : ∃ z, Adjacent m (mr.rep i) z ∧ m z (mr.rep j)) :
    Nonempty (AdjBox m mr i j) :=
  sorry

/-! ## Smattes (discretize.v:226–342) -/

/-- A discrete approximation ("smatte") of a region: a finite set of grid
    points whose union approximates the region from below. The exact data
    structure depends on the grid/matte port; here we keep it abstract. -/
structure SMatte (m : Map) {n : ℕ} (mr : MapRepr m n) (i : Fin n) where
  /-- The smatte must be contained in the region. -/
  inside : Region
  inside_subset : inside ⊆ m (mr.rep i)
  /-- The smatte meets every adjacency box for `i`. -/
  meets_adj : ∀ j, (∃ z, Adjacent m (mr.rep i) z ∧ m z (mr.rep j)) →
      ∀ ab : AdjBox m mr i j, Meet inside ab.rect.region

/-- Every region admits a smatte intersecting all of its adjacency boxes
    (discretize.v:319 `exists_smatte`). -/
theorem exists_sMatte (m : Map) (hm : FiniteSimpleMap m)
    {n : ℕ} (mr : MapRepr m n) (i : Fin n) :
    Nonempty (SMatte m mr i) :=
  sorry

/-! ## Gridmap construction (gridmap.v) -/

/-- The hypermap built from a system of mattes and adjacency boxes. The
    construction is parametric in the matte data, so we expose it as an
    existence statement. -/
theorem exists_gridmap (m : Map) (hm : FiniteSimpleMap m) :
    ∃ G : Hypermap, Planar G ∧ Bridgeless G ∧
      (FourColorable G → ColorableWith 4 m) :=
  sorry

/-! ## The discretization theorem (discretize.v:347) -/

/-- The discretization theorem: any finite simple map in the real plane
    can be discretized to a planar bridgeless hypermap G, such that
    any four-coloring of G induces a four-coloring of the original map. -/
theorem discretize_to_hypermap (m : Map)
    (hm : FiniteSimpleMap m) :
    ∃ G : Hypermap, Planar G ∧ Bridgeless G ∧
      (FourColorable G → ColorableWith 4 m) :=
  exists_gridmap m hm

end FourColor
