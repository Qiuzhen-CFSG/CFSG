module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveFlagAutomorphisms.Representation
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveActor.MarkedCoefficient


/-!
# The actual original U₅ outer involution is a unitary graph twist

The same reversed marked action, native lift and full common-normalizer
comparison determine the literal residual coefficient. The native representation
theorem then gives one unitary matrix for that same original middle actor.
Both covers, both admitted orientations, and the original KnownSimple scope
are retained; no quotient conjugator is substituted for the whole actor.

Source: Aschbacher–Smith F.4.29(2), printed p.289 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.UnitaryFiveFlagAutomorphisms
open Theory.SpecificGroups.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- Representation of the SAME original actor supplied by the full-normalizer comparison. -/
theorem Preparation.unitaryFive_marked_actor_unitary_graph
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
    ∃ u : U.form.unitarySubgroup,
      (F.middle t).val = Descent.unitaryConj U.form u * GraphFixed.projectiveAut U.form U.matrix := by
  obtain ⟨hactor,hinv,hcoeff⟩ := d.unitaryFive_marked_actor_coefficient
    h hH hp U hc r a ell F hF t htT ht htS
  obtain ⟨u,hu⟩ := involution_eq_unitary_graph U (ell.action t) hinv hcoeff
  exact ⟨u,hactor.symm.trans hu⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
