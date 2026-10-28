module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.CertificateData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.SpanningCriterion
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Edges
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Spanning

/-!
# Assembly of the degree-1792 nucleus column certificate

The published earlier-parent tree starts at the literal nucleus. Its left-action
identities realize each candidate column by a word in the original untransposed
ATLAS generators. A separate coordinate reconstruction then proves that their
algebra orbit spans. The checked action and spanning certificates discharge both
numerical obligations, proving column cyclicity for every subalgebra containing
the two generators.

Source: ATLAS M24G1-f2r1792B0, with attribution and conventions in
`source/README.md`; candidate reproduction in `ColumnOrbit/source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792
open Matrix ColumnData

/-- Each checked predecessor edge is a left action by an original generator. -/
theorem columns_reachable_of_steps
    (hstep : ∀ i : Fin 1791,
      (if actor i then Data1792.first else Data1792.second).mulVec (column (parent i)) =
        column i.succ)
    (Q : Subalgebra (ZMod 2) (Matrix (Fin 1792) (Fin 1792) (ZMod 2)))
    (hA : Data1792.first ∈ Q) (hB : Data1792.second ∈ Q) :
    ∀ i : Fin 1792, ∃ L ∈ Q, L.mulVec nucleus = column i := by
  apply ColumnCertificate.orbit_reachable 1791 Q Data1792.first Data1792.second hA hB
    nucleus column parent actor
  · exact parent_lt
  · exact column_zero
  · exact hstep

/-- Final assembly once the action and coordinate-span certificates are checked. -/
theorem columnOrbit_eq_top_of_steps_and_span
    (hstep : ∀ i : Fin 1791,
      (if actor i then Data1792.first else Data1792.second).mulVec (column (parent i)) =
        column i.succ)
    (hspan : Submodule.span (ZMod 2) (Set.range column) = ⊤)
    (Q : Subalgebra (ZMod 2) (Matrix (Fin 1792) (Fin 1792) (ZMod 2)))
    (hA : Data1792.first ∈ Q) (hB : Data1792.second ∈ Q) :
    Submodule.span (ZMod 2) (Set.range (fun L : Q => L.val.mulVec nucleus)) = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  obtain ⟨L, hL, he⟩ := columns_reachable_of_steps hstep Q hA hB i
  exact Submodule.subset_span ⟨⟨L, hL⟩, he⟩

/-- The published nucleus has spanning column orbit under every subalgebra
containing the original untransposed ATLAS generators. This discharges the
column-orbit premise of `density1792_of_rankOne_and_columnOrbit`. -/
theorem columnOrbit_eq_top
    (Q : Subalgebra (ZMod 2) (Matrix (Fin 1792) (Fin 1792) (ZMod 2)))
    (hA : Data1792.first ∈ Q) (hB : Data1792.second ∈ Q) :
    Submodule.span (ZMod 2) (Set.range (fun L : Q => L.val.mulVec nucleus)) = ⊤ := by
  exact columnOrbit_eq_top_of_steps_and_span column_step column_span Q hA hB

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792
