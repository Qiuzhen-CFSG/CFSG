module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.TitsCubicDisplacement.ElementaryGeometry
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.TitsCubicDisplacement.InternalEstimate

/-!
# The actual representation consumer of the finite Tits calculations

The completed finite geometry removes all rank, commutator and centralizer
premises from the internal estimate. Binary involution coverage and the two
five-weight estimates retain their independent producers; the parent task
`qt-k03-tits-cubic-displacement` owns their final discharge. The earlier
application with explicit finite bounds is preserved below.

This application uses the original Parrott representation, its actual
five-kernel and the literal five-inverter. Source: GM04 Lemma 8.8, internal p.57.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement.ElementaryGeometry
open Subgroup Tits Tits.InvolutionRootGeometry
open Representation Representation.BinaryOffender

/-- The finite calculations feed the existing internal estimate on its
literal carrier, with explicit bounds for clients that supply them. -/
theorem internal_displacement_of_rank_and_root_bounds
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (hcover : BinaryInvolutionCoverage)
    (hrank : primeRank 2 ParrottGroup ≤ 5)
    (hlong : NormalElementaryBound (parrottGenerator .s1))
    (hshort : NormalElementaryBound (parrottGenerator .s4))
    (σ : Representation (ZMod 2) ParrottGroup V) (hf : Function.Injective σ)
    (hfive : ∀ k ∈ fiveKernel, k ≠ 1 → 20 ≤ fixedCodim σ (zpowers k))
    (hinverter : 12 ≤ fixedCodim σ (zpowers fiveInverter))
    (A : Subgroup ParrottGroup) (hA : IsElementaryTwo A) :
    2 * rank A < fixedCodim σ A :=
  internal_displacement_of_local_calculations
    (localGeometry_of_rank_and_root_bounds hcover hrank hlong hshort)
    σ hf hfive hinverter A hA

/-- The actual Parrott representation consumer with all finite group bounds
discharged. Only coverage and the independent five-weight estimates remain. -/
theorem internal_displacement_of_coverage_and_weights
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (hcover : BinaryInvolutionCoverage)
    (σ : Representation (ZMod 2) ParrottGroup V) (hf : Function.Injective σ)
    (hfive : ∀ k ∈ fiveKernel, k ≠ 1 → 20 ≤ fixedCodim σ (zpowers k))
    (hinverter : 12 ≤ fixedCodim σ (zpowers fiveInverter))
    (A : Subgroup ParrottGroup) (hA : IsElementaryTwo A) :
    2 * rank A < fixedCodim σ A :=
  internal_displacement_of_local_calculations (localGeometry_of_coverage hcover)
    σ hf hfive hinverter A hA

end CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement.ElementaryGeometry
