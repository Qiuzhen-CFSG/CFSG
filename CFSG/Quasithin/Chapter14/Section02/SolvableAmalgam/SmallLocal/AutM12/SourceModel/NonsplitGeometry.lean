module

public import Theory.Mathieu.M12.SmallParabolicPair.SwapCoreCoordinates
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.SourceQuotientBridge.NonsplitOther.Square
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.SourceQuotientBridge.Cubic
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.SourceModel.MarkedPair

/-!
# The actual Aut(M₁₂) quotient and compatible marked pair

The concrete first parabolic has the nonsplit core `outerCore`, with its
marked center `distinguished`. The actual quotient is `E₄ wr C₂`, and the
base is the image of the residual quaternion commutator. The coordinate
bridge preserves the kernel and actual first-parabolic conjugation. The
marked subgroup is also the image of Ω₁(Z(T)) for the whole overlap T.

`compatibleMarkedPair` instantiates the whole-overlap movement geometry,
including all four second-parabolic action equations and the literal natural
four. Its split movement subgroup is proved distinct from the first two-core.
The original `QuaternionSwapModel` and its marked M₁₂ core comparison remain
re-exported, with their original meanings.

The proposed unconditional elementary-sixteen lift in the actual first core
is impossible. Its other-eight preimage has order sixteen but contains the
actual swap of order four. In fact every elementary subgroup of that core
maps into the wreath base. Hence the split E₁₆ action and S₄ quotient cannot
be transported to this preimage. The marked equivalence with C₄ × E₄, the nonzero square functional on A/Z,
and the exact action of an explicit first-parabolic cubic are now exported.
The larger-ambient argument and aligned residual embeddings remain source
assembly obligations; this module does not assert completion of 14.2.21.

Source: Aschbacher–Smith, Lemma 14.2.21, printed p.988, PDF p.1005,
`refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.SourceModel
open Sporadic.Mathieu.M12ExceptionalExtension FirstParabolic

/-- The actual marked central quotient in the coordinates used by the source deduction. -/
def coreQuotient : OuterQuotient ≃* FourWreathTwo.Wreath :=
  SourceQuotientBridge.quotientEquiv innerModel

/-- The quotient map is defined on the ambient image of O₂(H). -/
def coreWreathMap : outerCore →* FourWreathTwo.Wreath :=
  SourceQuotientBridge.wreathMap innerModel

theorem coreQuotient_mk (x : outerCore) : coreQuotient (outerProjection x) = coreWreathMap x :=
  rfl

theorem coreWreathMap_surjective : Function.Surjective coreWreathMap :=
  SourceQuotientBridge.wreathMap_surjective innerModel

theorem coreWreathMap_ker : coreWreathMap.ker = distinguished.subgroupOf outerCore :=
  SourceQuotientBridge.wreathMap_ker innerModel

theorem coreWreathMap_base :
    (quaternionCore.subgroupOf outerCore).map coreWreathMap = FourWreathTwo.base :=
  SourceQuotientBridge.wreathMap_base innerModel

/-- Conjugation by the actual first parabolic, on the actual quotient. -/
def coreAction : firstParabolic →* MulAut FourWreathTwo.Wreath :=
  SourceQuotientBridge.action innerModel

theorem coreAction_evaluation (h : firstParabolic) (x : outerCore) :
    coreAction h (coreWreathMap x) = coreWreathMap
      (outerConjugation (firstParabolic_normalizes_outerCore innerModel) h x) :=
  SourceQuotientBridge.action_evaluation innerModel h x

/-- The actual order-sixteen preimage; it is not the split model's E₁₆. -/
def otherPreimage : Subgroup outerCore := SourceQuotientBridge.otherPreimage innerModel

theorem otherPreimage_card : Nat.card otherPreimage = 16 :=
  SourceQuotientBridge.otherPreimage_card innerModel

theorem otherPreimage_not_elementary : ¬ IsElementaryAbelian 2 otherPreimage :=
  SourceQuotientBridge.otherPreimage_not_elementary innerModel

theorem otherPreimage_not_equiv_E16 :
    ¬ Nonempty (otherPreimage ≃* QuaternionSwapModel.E16) :=
  SourceQuotientBridge.otherPreimage_not_equiv_E16 innerModel

/-- The actual marked C₄ × E₄ identification. -/
def otherPreimageEquiv : otherPreimage ≃* SourceQuotientBridge.NonsplitOther.Coordinates :=
  SourceQuotientBridge.NonsplitOther.markedEquiv innerModel

theorem otherPreimageEquiv_marked : otherPreimageEquiv
    ⟨outerMarked,SourceQuotientBridge.NonsplitOther.marked_mem innerModel⟩ =
      (Multiplicative.ofAdd 2, 1) :=
  SourceQuotientBridge.NonsplitOther.markedEquiv_marked innerModel

abbrev otherMarkedSubgroup := SourceQuotientBridge.NonsplitOther.markedSubgroup innerModel
abbrev OtherQuotient := otherPreimage ⧸ otherMarkedSubgroup

def otherQuotientEquiv : OtherQuotient ≃* FourWreathTwo.other :=
  SourceQuotientBridge.NonsplitOther.centralQuotientEquiv innerModel

theorem otherQuotient_card : Nat.card OtherQuotient = 8 :=
  SourceQuotientBridge.NonsplitOther.centralQuotient_card innerModel

instance otherQuotient_elementary : IsElementaryAbelian 2 OtherQuotient :=
  SourceQuotientBridge.NonsplitOther.centralQuotient_elementary innerModel

/-- The actual square map, retaining its original marked codomain. -/
def otherSquare : OtherQuotient →* distinguished :=
  SourceQuotientBridge.NonsplitOther.squareMap innerModel

theorem otherSquare_mk (x : otherPreimage) :
    (otherSquare (QuotientGroup.mk' otherMarkedSubgroup x)).val = x.val.val ^ 2 := rfl

theorem otherSquare_nonzero : otherSquare ≠ 1 :=
  SourceQuotientBridge.NonsplitOther.squareMap_nonzero innerModel

theorem otherSquare_ker_card : Nat.card otherSquare.ker = 4 :=
  SourceQuotientBridge.NonsplitOther.squareMap_ker_card innerModel

/-- This element belongs to the actual first parabolic. -/
def coreCubic : firstParabolic := SourceQuotientBridge.alignedCubic innerModel

theorem coreAction_coreCubic : coreAction coreCubic = FourWreathTwo.cubic :=
  SourceQuotientBridge.action_alignedCubic innerModel

theorem coreCubic_conjugation (x : outerCore) :
    coreWreathMap (outerConjugation (firstParabolic_normalizes_outerCore innerModel)
      coreCubic x) = FourWreathTwo.cubic (coreWreathMap x) :=
  SourceQuotientBridge.alignedCubic_conjugation innerModel x

theorem firstParabolic_card : Nat.card firstParabolic = 384 :=
  FirstParabolic.card_firstParabolic innerModel

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.AutM12.SourceModel
