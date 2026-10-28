module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.Assembly
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeSection
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.DualAction.Commutator

/-!
# Native conjugation and quintet inputs for the hexad code

The H.14 natural coordinates supply the literal conjugation marking of the
hexad kernel. The established quintet cocode flag has fixed dimension one.
Its middle module is indecomposable, and a nonidentity inner-core involution
has displacement four. The existing commutator argument therefore identifies
the quintet code fixed space with its geometric four-dimensional annihilator.
These discharge the remaining native inputs of the hexad code assembly.

Source: Aschbacher--Smith H.14.3(2--3), H.15.4(1--2), H.16.3(1), and
H.16.4, printed pp.397,400,403, refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Sporadic.Mathieu Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace MathieuCode.Hexad.NativeInputs

/-- The natural H.14 marking retains literal conjugation in the pair group. -/
def kernelConjugation : Assembly.KernelConjugationInput where
  quotientMap := M22ChapterH.Hexad.Action.Natural.outerMap
  quotientMap_surjective := M22ChapterH.Hexad.Action.Natural.outerMap_surjective
  quotientMap_ker := M22ChapterH.Hexad.Action.Natural.outerMap_ker_subgroupOf
  marking := M22ChapterH.Hexad.Action.Natural.outerKernel.symm
  conjugation g v := (M22ChapterH.Hexad.Action.Natural.outerKernel_conjugation g v).symm

open M22Quintet M22Quintet.CocodeTransfer
open NormalizedShadowRows

/-- The two earlier H.14 facts consumed by quintet code duality. -/
theorem quintetEarlier : DualAction.EarlierInputs M22CodeSection.actionData where
  indecomposable := M22ChapterH.Quintet.kernelConjugation_indecomposable
  involution_displacement := by
    have hn : A0 ≠ ⊥ := by
      intro he
      have hc := M22ChapterH.Quintet.innerIntersection_card
      change Nat.card A0 = 16 at hc
      rw [he, Subgroup.card_bot] at hc
      omega
    obtain ⟨i, hi⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hn
    have hin : i.val ≠ 1 := fun he => hi (Subtype.ext he)
    have hp : i.val ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian i.val i.property.1
    have ho : orderOf i.val = 2 := orderOf_eq_prime hp hin
    refine ⟨⟨i.val, i.property.1⟩, i.property.2, ?_, Subtype.ext hp, ?_⟩
    · exact fun he => hin (congrArg Subtype.val he)
    · change Module.finrank (ZMod 2)
        (LinearMap.range (m22OuterCocodeRepresentation i.val - LinearMap.id)) = 4
      have hd := fixedCodim_add_finrank m22OuterCocodeRepresentation (Subgroup.zpowers i.val)
      rw [M22ChapterH.Quintet.inner_involution_fixed i.val i.property.2 ho,
        finrank_m22Cocode, fixedCodim_zpowers_eq_displacement_rank] at hd
      omega

/-- Both scalar quintet inputs are consequences of the actual native actions. -/
theorem quintetDimensions : ChiefFlag.QuintetDimensions where
  cocode_fixed := M22CodeSection.flag.dim1
  code_fixed := by
    rw [← DualAction.V4_eq_fixedSpace M22CodeSection.actionData quintetEarlier]
    exact M22CodeFourSpace.finrank_four

end MathieuCode.Hexad.NativeInputs
