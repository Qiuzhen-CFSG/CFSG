module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveActor.QuotientTransport
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.OuterSylow

/-!
# The quotient input for the original marked outer actor

For any marking returned by `unitaryFive_marked_outer_saturated`, use its
same middle equation and same native lift. Every original outer involution
is thus a native flag involution with Hermitian coefficient. The statement
applies to the selected saturated involution while retaining its original
extension and both saturation clauses; it requires only their middle equation.
Full unitary-twist representation remains the missing native rigidity theorem.

Source: F.4.29(2), and its use in F.4.37, printed pp.289,293 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.UnitaryFiveFlagAutomorphisms
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- The exact original middle actor meets the native representation theorem's
involution and coefficient hypotheses. No quotient marking is supplied. -/
theorem Preparation.unitaryFive_marked_actor_coefficient
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
    (ell.action t).val = (F.middle t).val ∧
      (ell.action t) ^ 2 = 1 ∧ rightCoefficient U (ell.action t) = U.form.conj := by
  refine ⟨(hF t).symm, ?_, d.unitaryFive_lift_rightCoefficient h hH hp U hc a ell t htT ht htS⟩
  have ht2 : t ^ 2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
  rw [← map_pow, ht2, map_one]

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
