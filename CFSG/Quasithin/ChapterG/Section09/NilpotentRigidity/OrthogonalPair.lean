module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.Contracts
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.OrthogonalPair.ModuleRecognition

/-!
# The natural orthogonal action of a dihedral pair

This proves the precise small-model contract used in the equality cases
of Aschbacher--Smith G.9.2, printed pp.352--353 (`refs/quasithin.pdf`,
PDF pp.363--364). The determinant action identifies the dihedral product
with the actual Siegel-generated `OmegaFour`. The rotation orbit of a
common reflection-fixed vector supplies the intertwining linear
equivalence for every four-dimensional module in the contract.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity

universe v

/-- The unconditional carrier-and-action identification required by the
orthogonal four-space branch of G.9.2. -/
theorem orthogonalPairTheorem : OrthogonalPairTheorem.{v} := by
  intro W _ _ _ σ _ hdim hr hs
  obtain ⟨f, hf⟩ := ClassicalOrthogonal.BinaryD2.exists_intertwining_equiv σ hdim hr hs
  exact ⟨ClassicalOrthogonal.BinaryD2.pairEquiv, f, hf⟩

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity
