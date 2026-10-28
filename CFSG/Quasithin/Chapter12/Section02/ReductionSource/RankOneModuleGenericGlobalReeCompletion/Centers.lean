module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.Centers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeOvercomponent

/-!
# Long-root centralizer control for the original Chapter12 Ree pair

The compatible native comparison identifies the right residual center with
the long-root curve. Its actual torus orbit, right maximality and original
uniqueness give the full ambient centralizer bound. The center is nontrivial,
elementary abelian and TI, and its full normalizer is N_G(O²(H)). Both
comparison orientations are retained; the impossible one is excluded.

This supplies the original 5.3.3 long-root input and F.4.34 geometry.
The compatible native normalizer extension, short-root centralizer,
nonfusion and full-extension order comparison still remain before GlobalExit.
Source: Aschbacher–Smith 5.3.3, F.4.34 and 12.2.2,
printed pp.659,291,795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The full normalizer conditions and factor-center bounds for the actual
Chapter12 Ree comparison. No normalizer-action or centralizer premise is added. -/
theorem rankOne_global_ree_normalizer_centralizer_conditions
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
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse)) :
    Chapter5.Section03GreenExtension.SourceLocalConditions
      (Global.normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) ∧
    ∀ i : Fin 2, ∀ z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype,
      orderOf z = 2 → centralizer ({z} : Set G) ≤ normalizer (![L,residual H] i : Set G) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.ree_normalizer_local_conditions hi hH hp m he,
    d.ree_central_involution_centralizers hi hH hp m he⟩

/-- The nontrivial original right center is an elementary TI subgroup with
its literal full normalizer and full ambient long-involution centralizer bound. -/
theorem rankOne_global_ree_right_center_fusion
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
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse)) :
    (∃ z ∈ (center (residual H)).map (residual H).subtype, orderOf z = 2 ∧
      centralizer ({z} : Set G) ≤ normalizer (residual H : Set G)) ∧
    IsElementaryAbelian 2 ((center (residual H)).map (residual H).subtype) ∧
    IsTISubgroup ((center (residual H)).map (residual H).subtype) ∧
    normalizer (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) =
      normalizer (residual H : Set G) := by
  let hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  exact ⟨d.ree_right_center_involution hi hH hp m he,
    d.ree_right_center_fusion hi hH hp m he⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
