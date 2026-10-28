module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.TitsCubicDisplacement.LocalData
public import Theory.Representation.Tits.FrobeniusDisplacement
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# The two five-local Tits displacement estimates

The certified 5²:24 subgroup gives displacement at least twenty for each
nonidentity kernel element and at least twelve for the literal quaternion
square `fiveInverter`. These are exactly the two numerical inputs to
`internal_displacement_of_local_calculations`. The independent finite local
geometry remains with the source-theorem assembly.

Source: GM04 Lemma 8.8, internal p.57, DOI 10.1515/9783110198126.117;
see `Source.md` for the comparison with its degree-26 argument.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement
open Subgroup Representation Representation.BinaryOffender

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Every nonidentity element of the actual five-kernel moves twenty dimensions. -/
theorem fiveKernel_fixedCodim_ge_twenty
    (σ : Representation (ZMod 2) Tits.ParrottGroup V) (hf : Function.Injective σ)
    (k : Tits.ParrottGroup) (hk : k ∈ Tits.fiveKernel) (hne : k ≠ 1) :
    20 ≤ fixedCodim σ (zpowers k) := by
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact TitsFrobeniusDisplacement.fiveKernel_displacement σ hf ⟨k, hk⟩
    (fun h => hne (congrArg Subtype.val h))

/-- The literal quaternion-square inverter moves at least twelve dimensions. -/
theorem fiveInverter_fixedCodim_ge_twelve
    (σ : Representation (ZMod 2) Tits.ParrottGroup V) (hf : Function.Injective σ) :
    12 ≤ fixedCodim σ (zpowers fiveInverter) := by
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact TitsFrobeniusDisplacement.fiveInverter_displacement σ hf

end CFSG.Quasithin.ChapterK.Exceptional.TitsCubicDisplacement
