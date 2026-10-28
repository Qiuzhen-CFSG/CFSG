module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveFlagAutomorphisms.TorusNormalization
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveActor.MarkedCoefficient


/-!
# The original outer U₅ actor on the full plane radical

Retain the same original marking, reversed lift and middle map. Quotient
normalization, removal of the standard graph, and one native radical
conjugation give a full scalar formula on the entire plane radical. The
chosen torus is fixed, the remaining Levi displacement is central, and
the original involution cocycle is retained. Constructing a unitary matrix
and establishing opposite-endpoint agreement remain necessary.

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
theorem Preparation.unitaryFive_marked_actor_plane_normalize
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
    ∃ (b : U.overlap) (γ : flagAutomorphisms U) (k : U.F) (t₀ : U.Fˣ),
      b.val ∈ U.rightLocalImage ∧ k ≠ 0 ∧ orderOf t₀ = 15 ∧
      ell.action t = innerFlag U b * γ * graphFlag U ∧
      (F.middle t).val = MulAut.conj b.val * γ.val * GraphFixed.projectiveAut U.form U.matrix ∧
      rightLinearAction U γ = 1 ∧
      rightCoordinateAction U γ (SemidirectProduct.inr (PlaneCore.ResidualAction.diagonalActor t₀)) =
        SemidirectProduct.inr (PlaneCore.ResidualAction.diagonalActor t₀) ∧
      (∀ u : PlaneCore.Parameters U.form, (rightRadicalAction U γ u).x = k • u.x) ∧
      (∀ u : PlaneCore.Parameters U.form, (rightRadicalAction U γ u).z = (k * U.form.conj k) • u.z) ∧
      (∀ A : Matrix.SpecialLinearGroup (Fin 2) U.F,
        (FlagAutomorphisms.leviDeviation U.form (rightCoordinateAction U γ) A).x = 0) ∧
      (γ * graphFlag U) * innerFlag U b * (γ * graphFlag U) = (innerFlag U b)⁻¹ := by
  obtain ⟨hactor,hinv,hcoeff⟩ := d.unitaryFive_marked_actor_coefficient
    h hH hp U hc r a ell F hF t htT ht htS
  obtain ⟨b,γ,k,t₀,hb,hk,ht₀,he,hq,hfix,hx,hz,hcentral,hcocycle⟩ :=
    involution_plane_normalize U (ell.action t) hinv hcoeff
  refine ⟨b,γ,k,t₀,hb,hk,ht₀,he,?_,hq,hfix,hx,hz,hcentral,hcocycle⟩
  rw [←hactor,he]
  rfl

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
