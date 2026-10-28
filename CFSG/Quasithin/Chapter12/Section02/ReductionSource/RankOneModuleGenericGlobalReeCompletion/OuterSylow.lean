module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.OuterSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeCompletion.FullNormalizer

/-!
# Original Chapter12 Ree extension degree and Sylow marking

The original chosen whole-residual pair supplies the full-normalizer
extension together with its cyclic odd outer degree, exact O^{2′}, order
factorization and the image of the original ambient Sylow. The same
witness retains both endpoint markings and the entire Borel overlap.
No extension, outer-degree or Sylow-realization premise is added.
The full ambient order bound and hence GlobalExit remain to be proved.

Source: Aschbacher–Smith 5.3.1–3, F.4.38,43 and 12.2.2,
printed pp.658–659,294,296,795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original chosen pair has a full extension of odd degree dividing the
same field degree, with its original ambient Sylow mapped through the full overlap. -/
theorem rankOne_global_ree_full_extension_outer_sylow
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
    2*m+1 = n ∧ 0 < m ∧
    ∃ R : Global.ReeNormalizerMarking L (residual H) (Global.sourceS L H) m,
      let J := (MulAut.innerSubgroup (ReeF4.Model m)).subgroupOf R.extension.carrier
      J.index ∣ 2*m+1 ∧ Odd J.index ∧ IsCyclic (R.extension.carrier ⧸ J) ∧
      primeToResidual 2 R.extension.carrier = J ∧
      Nat.card R.extension.carrier = J.index * Nat.card (ReeF4.Model m) ∧
      (T : Subgroup G) ≤ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ∧
      ∃ S : Sylow 2 R.extension.carrier,
        (S : Subgroup R.extension.carrier) =
          ((T : Subgroup G).subgroupOf (normalizer (L : Set G) ⊓
            normalizer (residual H : Set G))).map R.middleToCarrier := by
  exact d.ree_full_extension_outer_sylow
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
