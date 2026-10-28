module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveFlagAutomorphisms.BorelNormalization
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveActor.MarkedCoefficient

/-!
# Native Levi normalization of the original outer U₅ actor

The same full-normalizer marking and reversed lift identify the original
outer involution's native coefficient with Hermitian conjugation. The actual
flag constrains its quotient inner factor to the Borel, and the native plane
Levi removes that factor. Both the literal original middle equation and the
resulting cocycle equation are retained. No radical or opposite-endpoint
formula is assumed or concluded here.

Source: F.4.29(2), printed p.289 of refs/quasithin.pdf. Completing the whole
unitary-twist representation still requires rigidity on both parabolics.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.UnitaryFiveFlagAutomorphisms
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- Normalize the exact original actor with a native flag element, retaining
the quotient action and the original involution constraint. -/
theorem Preparation.unitaryFive_marked_actor_quotient_normalize
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U)
    (a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L)
      U.amalgam.reverse)
    (ell : UnitaryNativeLift.Five.LiftReverse U a)
    (F : RankTwoAmalgam.Iso (UnitaryCompletion.normalizerDiagram L (residual H))
      r.extension.amalgam.reverse)
    (hF : ∀ z, (F.middle z).val = (ell.action z).val)
    (t : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G))
    (htT : t.val ∈ (T : Subgroup G)) (ht : orderOf t = 2)
    (htS : t.val ∉ sourceS L H) :
    ∃ (b : U.overlap) (β : flagAutomorphisms U),
      b.val ∈ U.rightLocalImage ∧
      ell.action t = innerFlag U b * β ∧
      (F.middle t).val = MulAut.conj b.val * β.val ∧
      rightLinearAction U β = Theory.PSL2.fieldAut U.form.conj ∧
      β * innerFlag U b * β = (innerFlag U b)⁻¹ := by
  obtain ⟨hactor,hinv,hcoeff⟩ := d.unitaryFive_marked_actor_coefficient
    h hH hp U hc r a ell F hF t htT ht htS
  obtain ⟨b,β,hb,he,hq,hcocycle⟩ := rightLinearAction_normalize_involution U (ell.action t) hinv
  refine ⟨b,β,hb,he,?_,hcoeff ▸ hq,hcocycle⟩
  rw [←hactor,he]
  rfl

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
