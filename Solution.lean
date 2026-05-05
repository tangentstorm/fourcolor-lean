/-
Solution module for the leanprover/comparator tool.

Re-exports the headline theorems from the `FourColor` library. Comparator
checks that the propositions of `four_color`, `four_color_finite`, and
`four_color_hypermap` here match those declared (as `sorry`) in
`Challenge.lean`, and that the proof axioms match `permitted_axioms` in
`config.json`.

While there are still open `sorry`s downstream in the FourColor library,
comparator will reject this solution. Once the chain is closed it will accept.
-/
import FourColor

set_option maxHeartbeats 400000

-- The fully-qualified names `FourColor.four_color`, `FourColor.four_color_finite`,
-- and `FourColor.four_color_hypermap` are exported transitively from
-- `FourColor.FourColor` and `FourColor.Combinatorial4ct`.
