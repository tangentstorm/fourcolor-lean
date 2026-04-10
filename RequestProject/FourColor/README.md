# Four Color Theorem — Lean 4 Port

Lean 4 port of the Gonthier et al. formal proof of the Four Color Theorem
(originally ~45,000 lines of Coq across 119 files).

## Architecture

| File | Description | Status |
|------|-------------|--------|
| `Hypermap.lean` | Core hypermap structure (finite type + 3 permutations with triangular identity) | Core definitions and cancellation/injectivity lemmas fully proved |
| `Color.lean` | Four colors with XOR arithmetic, edge permutations, traces | Fully proved |
| `Geometry.lean` | Geometric properties: bridgeless, plain, cubic, pentagonal, rings | Definitions complete |
| `Coloring.lean` | Map coloring, four-colorability, contracts, minimal counter-examples | Definitions and `four_colorable_bridgeless` proved |
| `Walkup.lean` | Walkup construction for removing darts from hypermaps | Correct `skipEdge1` construction with triangular identity proved |
| `Jordan.lean` | Equivalence of Euler and Jordan planarity | `euler_inequality` proved; Jordan equivalences pending |
| `Cube.lean` | Cube construction reducing coloring to cubic maps | `plain_cube`, `cubic_cube`, `cube_colorable`, `bridgeless_cube`, `cface_sym` all proved |
| `Configurations.lean` | 633 reducible configurations infrastructure | Definitions only |
| `Unavoidability.lean` | Discharge method (unavoidable set theorem) | Statement only |
| `Combinatorial4ct.lean` | Combinatorial Four Color Theorem | `four_color_hypermap` proved (modulo dependencies) |
| `RealPlane.lean` | Real plane topology (maps, regions, adjacency, coloring) | Definitions complete |
| `Discretize.lean` | Discretization of plane maps to hypermaps | Statement only |
| `Finitize.lean` | Compactness extension to infinite maps | Statement only |
| `FourColor.lean` | Top-level Four Color Theorem statement | `four_color` and `four_color_finite` proved (modulo dependencies) |

## What is Fully Proved

### Hypermap Fundamentals
- All 3 cancellation lemmas (`edgeK`, `faceK`, `nodeK`)
- Injectivity, surjectivity, bijectivity of edge/node/face permutations
- Dual and mirror constructions with verified triangular identities
- Euler inequality (`euler_le`): `eulerRhs G ≤ eulerLhs G`

### Color Arithmetic
- All properties of the 4-color XOR group (commutativity, associativity, self-inverse, cancellation)
- Bit operations and color construction

### Cube Construction
- Triangular identity (`cube_cancel3`)
- Plainness (`plain_cube`)
- Cubicity (`cubic_cube`)
- **Bridgelessness preservation** (`bridgeless_cube`): both directions proved
- **Coloring transfer** (`cube_colorable`): if cube G is 4-colorable, so is G
- **Face connectivity symmetry** (`cface_sym`): cface is a symmetric relation

### Walkup Construction
- Correct `skipEdge1` function matching the Coq definition
- Well-definedness of skip functions on subtypes (`skip1_ne`, `skipEdge1_ne`)
- Triangular identity for WalkupE (`edgeK` in walkupE)
- Cardinality theorem (`card_walkupE`)
- WalkupN and WalkupF defined via mirror/dual

### Coloring Theory
- `four_colorable_bridgeless`: 4-colorable ⟹ bridgeless

### Top-level Proof Chain (modulo dependencies)
- `four_color_hypermap`: every planar bridgeless hypermap is 4-colorable
  (via cube + strong induction + unavoidability + reducibility)
- `four_color_finite`: every finite simple map is 4-colorable
  (via discretization + four_color_hypermap)
- `four_color`: every simple map is 4-colorable
  (via compactness extension + four_color_finite)

## Remaining `sorry` Instances (14)

The remaining sorries correspond to the deepest mathematical content:

1. **Even genus property** (`even_genusP` in Hypermap.lean): The Euler
   characteristic difference is always even. Requires Walkup induction
   (~500 lines in Coq).

2. **Jordan-Euler equivalence** (3 sorries in Jordan.lean): Proving that
   the Euler planarity condition (genus = 0) is equivalent to the Jordan
   property (no Möbius paths). Requires Walkup induction (~2000 lines in Coq).

3. **Walkup planarity/Jordan preservation** (2 sorries in Walkup.lean):
   Planarity and Jordan property are preserved by Walkup transforms.
   Part of the Jordan-Euler proof infrastructure.

4. **Planarity preservation by cube** (1 sorry in Cube.lean): Proving
   genus G = 0 ↔ genus (cube G) = 0. Requires orbit counting analysis.

5. **Configuration reducibility** (4 sorries in Configurations.lean):
   Definition and verification of the 633 reducible configurations.
   In Coq, this is ~30,000 lines of computational reflection.

6. **Unavoidability** (1 sorry in Unavoidability.lean): The discharge
   method showing every planar map contains a reducible configuration.
   ~5,000 lines in Coq.

7. **Discretization** (1 sorry in Discretize.lean): Converting finite
   simple maps to planar bridgeless hypermaps.

8. **Compactness** (1 sorry in Finitize.lean): Extending from finite
   to arbitrary simple maps.

## Correspondence to Coq Files

| Lean File | Coq Files |
|-----------|-----------|
| Hypermap.lean | hypermap.v |
| Color.lean | color.v |
| Geometry.lean | geometry.v |
| Coloring.lean | coloring.v, chromogram.v |
| Walkup.lean | walkup.v |
| Jordan.lean | jordan.v |
| Cube.lean | cube.v |
| Configurations.lean | configurations.v, cfmap.v, cfcolor.v, cfcontract.v, cfquiz.v, cfreducible.v |
| Unavoidability.lean | discharge.v, hubcap.v, part.v, redpart.v |
| Combinatorial4ct.lean | combinatorial4ct.v |
| RealPlane.lean | realplane.v |
| Discretize.lean | discretize.v, gridmap.v, grid.v, matte.v |
| Finitize.lean | finitize.v |
| FourColor.lean | fourcolor.v |
