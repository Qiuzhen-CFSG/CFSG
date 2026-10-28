module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ChartData
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.KernelExact
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart

/-!
# The actual split A₂ × A₂ subsystem for Ree unitary descent

The explicit short-root chart gives a faithful full SL₃ factor in the literal
algebraic F₄ carrier. Exceptional duality and inverse Frobenius construct the
long factor. Their root curves commute, their product has exactly the diagonal
cubic center as kernel, and the checked Weyl word intertwines the original Ree
twist with the precise two-factor signed Frobenius convention.

Thus `SubsystemData` is constructed over every algebraically closed field of
characteristic two, without a representation, kernel or twist hypothesis.
`Subsystem.Application` applies it to the full unitary group and its Singer
and norm-one tori in the original finite Ree matrix model.
Source: GLS3 §2.6.2, Example 2.6.3 and Table 4.7.3A.
-/

@[expose] public noncomputable section
namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem
open ReeF4.CentralCovers.OddPrimary.Cyclotomic
open TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.ShortA2
variable (F : Type*) [Field F] [IsAlgClosed F] [CharP F 2]

/-- The complete two-factor construction, with no geometric premise remaining. -/
def data (m : ℕ) : SubsystemData m F :=
  dataOfChart (ShortChart.chart F) (ShortChart.chart_intertwines F) m

/-- Its kernel is precisely the diagonal center of the original full SL₃ factors. -/
theorem data_kernel_iff (m : ℕ) (A B : SL3 F) :
    (data F m).map (A,B) = 1 ↔ A = B ∧ A ∈ Subgroup.center (SL3 F) := by
  let f := SourceBlocks.matrixHom F (ShortChart.chart F)
  have hf := chart_matrix_marking (ShortChart.chart F) (ShortChart.chart_intertwines F)
  have hi : Function.Injective (pointMap f hf) :=
    pointMap_injective f hf (SourceBlocks.matrixHom_injective F (ShortChart.chart F))
  exact pairMap_kernel_iff (longMap (pointMap f hf)) (pointMap f hf)
    (longMap_marked (pointMap_marked f hf)) (pointMap_marked f hf)
    (longMap_injective _ hi) hi A B

/-- The original split-subsystem existence obligation is discharged. -/
theorem nonempty_data (m : ℕ) : Nonempty (SubsystemData m F) := ⟨data F m⟩

end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem
