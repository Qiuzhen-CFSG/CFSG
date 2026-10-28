module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.Thompson
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.LongRoot
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFullNormalizer.Five
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.GroupTheory.TwoInvolutionClassOrder

/-!
# Long-root centralizers on the published unitary-five marking

The original ambient long-root centralizer lies in the whole-residual
normalizer. Restricting that centralizer and applying the endpoint equivalence
of the published marking gives its order on the same extension. Both
orientations retain the literal endpoint equations and whole-overlap equation.

This transports the ambient part of F.4.31(b); identifying the endpoint
centralizer with the full extension centralizer remains a separate step.
Source: Aschbacher–Smith F.4.31(b), F.4.34 and F.4.43, printed pp.291,296.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem centralizer_card_in_endpoint {B : Type*} [Group B]
    (M : Subgroup G) (e : M ≃* B) (z : M)
    (hc : centralizer ({z.val} : Set G) ≤ M) :
    Nat.card (centralizer ({z.val} : Set G)) =
      Nat.card (centralizer ({e z} : Set B)) :=
  (Nat.card_congr (TwoInvolutionClassOrder.centralizerEquiv M z hc)).symm.trans
    (Nat.card_congr (CentralizerSmallKernelTransport.centralizerEquiv e z).toEquiv)

variable {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The published marking transports each full ambient long-root centralizer
into the literal endpoint centralizer on its same extension. The native
endpoint equations and whole-D equation are retained on the chosen maps.
No equality with the full extension centralizer is asserted here. -/
theorem Preparation.unitaryFive_marked_long_centralizers
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U) :
    (∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam,
      ∃ f : UnitaryNativeLift.Five.Lift U a,
      ∃ F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
          r.extension.amalgam,
        (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
        (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
        (∀ z, (F.middle z).val = (f.action z).val) ∧
        (∀ z : normalizer (residual H : Set G),
          z.val ∈ (center (residual H)).map (residual H).subtype → orderOf z.val = 2 →
          Nat.card (centralizer ({z.val} : Set G)) =
            Nat.card (centralizer ({F.right z} : Set r.extension.right)))) ∨
    (∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) U.amalgam.reverse,
      ∃ f : UnitaryNativeLift.Five.LiftReverse U a,
      ∃ F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
          r.extension.amalgam.reverse,
        (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
        (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
        (∀ z, (F.middle z).val = (f.action z).val) ∧
        (∀ z : normalizer (residual H : Set G),
          z.val ∈ (center (residual H)).map (residual H).subtype → orderOf z.val = 2 →
          Nat.card (centralizer ({z.val} : Set G)) =
            Nat.card (centralizer ({F.right z} : Set r.extension.left)))) := by
  have hbound := d.unitaryFive_central_involution_centralizers h hH hp U hc 1
  rcases r.marking with ⟨a,f,F,hF0,hF1,hFD,_⟩ | ⟨a,f,F,hF0,hF1,hFD,_⟩
  · exact Or.inl ⟨a,f,F,hF0,hF1,hFD,fun z hz ho =>
      centralizer_card_in_endpoint _ F.right z (hbound z hz ho)⟩
  · exact Or.inr ⟨a,f,F,hF0,hF1,hFD,fun z hz ho =>
      centralizer_card_in_endpoint _ F.right z (hbound z hz ho)⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
