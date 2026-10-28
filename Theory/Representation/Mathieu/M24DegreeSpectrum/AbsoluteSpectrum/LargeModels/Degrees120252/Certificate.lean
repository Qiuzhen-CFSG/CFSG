module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras.Certificate
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Data

/-!
# Traversal checks for the M24 matrix certificates

The existing rank-one and orbit-basis criterion is independent of its M22
application. We reuse it here. Checking a map of all stored rows avoids
repeated indexed traversal of the left-hand matrix during kernel reduction.
The lemma below relates this check to the ordinary matrix product.

Source context: James's binary M24 modules, J. Algebra 27 (1973), 57–111.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252
open MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration
open FactorAlgebras.Certificate MatrixChecks

/-- A checked row traversal supplies the existing multiplication certificate. -/
theorem product_rows {n : ℕ} (a b c : List ℕ) (ha : a.length = n)
    (h : a.map (combineList b) = c) :
    ∀ i : Fin n, combineList b (entry a i.val) = entry c i.val := by
  intro i
  rw [← h]
  have hi : i.val < a.length := ha ▸ i.isLt
  simp only [entry, List.getElem?_map, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252
