module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.ExtremalSelection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeCompletion.ShortAmbient

/-!
# Chapter12 extremal Ree short-marker selection from original inputs

Native exhaustion and full-left-endpoint fusion are proved for the actual
marking, discharging the corresponding premises of the original short-marker
selection. The three Sylow comparisons, full centralizer map and original
radical and nonfusion conclusions are retained. Ambient F.4.42 containment
and the order/recognition assembly remain separate.
Source: Aschbacher--Smith F.4.27,35,40--42 and 12.2.2,
printed pp.288,292,294--295,795 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
open ReeF4 ReeF4.Parabolics ReeF4.EvenInvolutionGeometry
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original chosen-module data now suffice for simultaneous extremality
in the ambient group, its left normalizer and the same Ree extension. -/
theorem rankOne_global_ree_short_extremal_comparison_of_source
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse))
    (R : Global.ReeNormalizerMarking L (residual H) (Global.sourceS L H) m) :
    ∃ (t : Model m) (v : normalizer (L : Set G)),
      IsShortRootInvolution t ∧ t ∈ radical m .linear ∧
      v.val ∈ L.pCoreIn 2 ∧ v.val ∈ T ∧ orderOf v.val = 2 ∧
      R.leftToCarrier v = R.extension.baseHom t ∧
      ((centralizer ({v.val} : Set G)).subgroupOf (normalizer (L : Set G))).map
        R.leftToCarrier = centralizer ({R.extension.baseHom t} : Set R.extension.carrier) ∧
      (∃ Q : Sylow 2 (centralizer ({v} : Set (normalizer (L : Set G)))),
        (Q : Subgroup (centralizer ({v} : Set (normalizer (L : Set G))))) =
          ((T : Subgroup G).subgroupOf (normalizer (L : Set G))).subgroupOf
            (centralizer ({v} : Set (normalizer (L : Set G))))) ∧
      (∃ Q : Sylow 2 (centralizer ({v.val} : Set G)),
        (Q : Subgroup (centralizer ({v.val} : Set G))) =
          (T : Subgroup G).subgroupOf (centralizer ({v.val} : Set G))) ∧
      (∃ S : Sylow 2 R.extension.carrier,
        (S : Subgroup R.extension.carrier) =
          ((T : Subgroup G).subgroupOf (normalizer (L : Set G) ⊓
            normalizer (residual H : Set G))).map R.middleToCarrier ∧
        R.extension.baseHom t ∈ S ∧
        ∃ Q : Sylow 2 (centralizer ({R.extension.baseHom t} : Set R.extension.carrier)),
          (Q : Subgroup (centralizer ({R.extension.baseHom t} : Set R.extension.carrier))) =
            (S : Subgroup R.extension.carrier).subgroupOf
              (centralizer ({R.extension.baseHom t} : Set R.extension.carrier))) ∧
      3 ∣ Nat.card (solvableResidual (centralizer ({v.val} : Set G))) ∧
      ∀ z ∈ (center (residual H)).map (residual H).subtype,
        orderOf z = 2 → ¬ IsConj z v.val := by
  exact d.ree_short_extremal_comparison_of_source
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m he R

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
