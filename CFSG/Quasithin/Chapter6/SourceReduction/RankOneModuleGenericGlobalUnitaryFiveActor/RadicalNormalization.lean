module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveFlagAutomorphisms.RadicalNormalization
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveActor.MarkedCoefficient


/-!
# Radical scalar normalization of the original outer U₅ actor

For the same original full-normalizer marking, reversed lift and middle actor,
remove the native quotient Levi factor and standard graph. The remaining
actor has identity quotient action and one nonzero scalar on the radical
vector quotient, with its norm on the full center. The original cocycle is
retained. No whole-actor unitary representation is claimed.

Source: Aschbacher–Smith F.4.29(2), printed p.289 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.UnitaryFiveFlagAutomorphisms
open Theory.SpecificGroups.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- Normalize the exact original actor with a native flag element, retaining
the quotient action and the original involution constraint. -/
theorem Preparation.unitaryFive_marked_actor_radical_normalize
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
    ∃ (b : U.overlap) (γ : flagAutomorphisms U) (k : U.F),
      b.val ∈ U.rightLocalImage ∧ k ≠ 0 ∧
      ell.action t = innerFlag U b * γ * graphFlag U ∧
      (F.middle t).val = MulAut.conj b.val * γ.val * GraphFixed.projectiveAut U.form U.matrix ∧
      rightLinearAction U γ = 1 ∧
      (∀ u : PlaneCore.Parameters U.form, (rightRadicalAction U γ u).x = k • u.x) ∧
      (∀ u : PlaneCore.Parameters U.form, u.x = 0 →
        (rightRadicalAction U γ u).z = (k * U.form.conj k) • u.z) ∧
      (γ * graphFlag U) * innerFlag U b * (γ * graphFlag U) = (innerFlag U b)⁻¹ := by
  obtain ⟨hactor,hinv,hcoeff⟩ := d.unitaryFive_marked_actor_coefficient
    h hH hp U hc r a ell F hF t htT ht htS
  obtain ⟨b,γ,k,hb,hk,he,hq,hx,hz,hcocycle⟩ :=
    involution_radical_normalize U (ell.action t) hinv hcoeff
  refine ⟨b,γ,k,hb,hk,he,?_,hq,hx,hz,hcocycle⟩
  rw [←hactor,he]
  rfl

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
