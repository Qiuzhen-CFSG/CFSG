module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.AmbientSylow
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveActor.Representation

/-!
# The full original Sylow subgroup is inner in the prepared U₅(4) row

If S<T, choose the original outer involution with both saturation clauses
on the given extension. Its proved representation is a unitary graph twist.
The invariant long-root intersection and full endpoint saturation place
C_T(t) in Syl₂(C_G(t)). The fixed-Sylow order bound contradicts the lower
bound from ambient involution fusion into the plane-core center.

The representation theorem is applied to the same marked action, lift and
whole-middle map. No new marking or extension is chosen.
Source: Aschbacher–Smith F.4.37–38, printed pp.293–294 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- F.4.38 for the original prepared row and the specified extension. -/
theorem Preparation.unitaryFive_sourceS_eq_sylow
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
    (r : UnitaryFiveNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) U) :
    sourceS L H = (T : Subgroup G) := by
  apply d.unitaryFive_sourceS_eq_sylow_of_actor_representation h hH hp U hc r
  intro a ell F _ _ hF t htT ht htS
  exact d.unitaryFive_marked_actor_unitary_graph h hH hp U hc r a ell F hF t htT ht htS

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
