module

public import Theory.Character.ClassSumFormula
-- Preserve the implementation access used by the existing `import all` clients.
import all Theory.Character.ClassSumFormula

/-!
# Compatibility entry point for the class-sum-character formula

The general class-sum formula now lives in `Theory.Character.ClassSumFormula`.
This module preserves its public declarations and the internal access used by
Bender--Glauberman's existing pair-count proofs.
-/
