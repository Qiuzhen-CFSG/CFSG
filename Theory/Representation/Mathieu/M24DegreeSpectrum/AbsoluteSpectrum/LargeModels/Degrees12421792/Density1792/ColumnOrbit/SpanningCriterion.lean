module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Data

/-!
# Coordinate reconstruction for the published nucleus columns

The sequential packed-vector reconstruction criterion is applied to the exact
candidate list. Reconstructing every standard coordinate from that list proves
its span is top. Numerical reconstruction identities remain explicit here.
Source data and bit convention: `source/README.md` and `../source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792
open ColumnCertificate ColumnData

/-- A checked reconstruction of all coordinates discharges the candidate span. -/
theorem column_span_of_reconstruction
    (h : ∀ i : Fin 1792, ∃ a, select a columns 0 = 2 ^ i.val) :
    Submodule.span (ZMod 2) (Set.range column) = ⊤ := by
  apply eq_top_of_reconstruction 1792 _ columns ?_ h
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi' : i < 1792 := by simpa only [columns_length] using hi
  apply Submodule.subset_span
  refine ⟨⟨i, hi'⟩, ?_⟩
  simp [column, hi]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792
