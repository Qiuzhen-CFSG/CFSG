module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.LongCentralizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeCompletion.OuterSylow

/-!
# The full long-root centralizer comparison for the original Chapter12 pair

The original chosen-module inputs identify the ambient long-root
centralizer's solvable residual with the whole original O²(H). They also
construct the same full-normalizer extension with its odd outer degree,
Sylow marking, and literal isomorphisms of the entire long-root centralizers.
The complete common-normalizer intersection and both parabolic markings
remain in that single witness, at every positive Ree parameter.

This supplies the long-root comparison used by F.4.43. Exhaustion of
involutions, full short-root centralizer control, and the ambient order
comparison remain required before recognition and GlobalExit.
Source: Aschbacher–Smith 5.3.1–3, F.4.27,35,43 and 12.2.2,
printed pp.658–659,288,291–292,296,795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The entire original long-root centralizer has exactly the whole original residual O²(H). -/
theorem rankOne_global_ree_long_centralizer_residual_eq
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
    (z : center (residual H)) (hz : orderOf z = 2) :
    (solvableResidual (centralizer ({z.val.val} : Set G))).map
      (centralizer ({z.val.val} : Set G)).subtype = residual H := by
  exact d.ree_long_centralizer_residual_eq
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m he z hz

/-- Full long-root centralizer isomorphisms in the same extension carrying the original Sylow. -/
theorem rankOne_global_ree_full_extension_long_centralizers
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
      (∃ S : Sylow 2 R.extension.carrier,
        (S : Subgroup R.extension.carrier) =
          ((T : Subgroup G).subgroupOf (normalizer (L : Set G) ⊓
            normalizer (residual H : Set G))).map R.middleToCarrier) ∧
      ∀ z : center (residual H), orderOf z = 2 →
        let zN : normalizer (residual H : Set G) :=
          ⟨z.val.val,(residual H).le_normalizer z.val.property⟩
        ((centralizer ({z.val.val} : Set G)).subgroupOf
          (normalizer (residual H : Set G))).map R.rightToCarrier =
            centralizer ({R.rightToCarrier zN} : Set R.extension.carrier) ∧
        Nonempty (centralizer ({z.val.val} : Set G) ≃*
          centralizer ({R.rightToCarrier zN} : Set R.extension.carrier)) := by
  exact d.ree_full_extension_long_centralizers
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
