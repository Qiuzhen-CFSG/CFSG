module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.TitsCubicDisplacement.ElementaryGeometry.Rank
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.TitsCubicDisplacement.ElementaryGeometry.InternalApplication

/-!
# The rank-five calculation in the Tits displacement argument

The unconditional rank bound discharges the numerical premise in the existing
local geometry and representation applications. Involution coverage and the
two relatively normal elementary centralizer bounds remain with their existing
owners, as do the five-weight displacement estimates.

Keeping this application separate lets the parent geometry assembly import
`Rank` without an import cycle. Source: GM04 Lemma 8.8, internal p.57, using
Table 13, p.53; Aschbacher–Smith K.3, printed p.457.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement.ElementaryGeometry
open Subgroup Tits Tits.InvolutionRootGeometry
open Representation Representation.BinaryOffender

/-- The rank premise in the local geometry is now discharged unconditionally. -/
theorem localGeometry_of_root_bounds (hcover : BinaryInvolutionCoverage)
    (hlong : NormalElementaryBound (parrottGenerator .s1))
    (hshort : NormalElementaryBound (parrottGenerator .s4)) : LocalGeometry :=
  localGeometry_of_rank_and_root_bounds hcover parrott_two_rank_le_five hlong hshort

/-- The actual Parrott representation consumer, with no separate rank premise. -/
theorem internal_displacement_of_root_bounds
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (hcover : BinaryInvolutionCoverage)
    (hlong : NormalElementaryBound (parrottGenerator .s1))
    (hshort : NormalElementaryBound (parrottGenerator .s4))
    (σ : Representation (ZMod 2) ParrottGroup V) (hf : Function.Injective σ)
    (hfive : ∀ k ∈ fiveKernel, k ≠ 1 → 20 ≤ fixedCodim σ (zpowers k))
    (hinverter : 12 ≤ fixedCodim σ (zpowers fiveInverter))
    (A : Subgroup ParrottGroup) (hA : IsElementaryTwo A) :
    2 * rank A < fixedCodim σ A :=
  internal_displacement_of_rank_and_root_bounds hcover parrott_two_rank_le_five
    hlong hshort σ hf hfive hinverter A hA

end CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement.ElementaryGeometry
