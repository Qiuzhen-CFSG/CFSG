module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.ShortCentralizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeCompletion.LongCentralizer

/-!
# The original Chapter12 short-root centralizer marking

The original prepared whole-residual comparison selects a short-root
involution in O₂(L). In the same full-normalizer extension carrying the
original Sylow and long-root comparisons, its full extension centralizer
is exactly the image of its original left-normalizer centralizer. Its
ambient centralizer has residual order divisible by three, so it is not
fused with any original long-root center involution.

All hypotheses are the original chosen-module inputs. The remaining
ambient containment C_G(t) ≤ N_G(L), involution exhaustion and F.4.43 order
comparison must still be proved before ambient recognition and GlobalExit.
Source: Aschbacher–Smith 5.3.1–3, F.4.27,35,42–43 and 12.2.2,
printed pp.658–659,288,292,295–296,795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
open ReeF4 ReeF4.Parabolics ReeF4.EvenInvolutionGeometry
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal original normalizer-centralizer comparison at the selected short-root marker. -/
theorem rankOne_global_ree_short_centralizer_comparison
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
      v.val ∈ L.pCoreIn 2 ∧ orderOf v.val = 2 ∧
      R.leftToCarrier v = R.extension.baseHom t ∧
      ((centralizer ({v.val} : Set G)).subgroupOf (normalizer (L : Set G))).map
        R.leftToCarrier = centralizer ({R.extension.baseHom t} : Set R.extension.carrier) ∧
      Nonempty (((centralizer ({v.val} : Set G)).subgroupOf (normalizer (L : Set G))) ≃*
        centralizer ({R.extension.baseHom t} : Set R.extension.carrier)) ∧
      3 ∣ Nat.card (solvableResidual (centralizer ({v.val} : Set G))) ∧
      ∀ z ∈ (center (residual H)).map (residual H).subtype,
        orderOf z = 2 → ¬ IsConj z v.val := by
  exact d.ree_short_centralizer_comparison
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m he R

/-- One extension retains both endpoint markings, the whole overlap, the Sylow, and the long- and short-root centralizer comparisons. -/
theorem rankOne_global_ree_full_extension_short_centralizers
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
      (∀ z : center (residual H), orderOf z = 2 →
        let zN : normalizer (residual H : Set G) :=
          ⟨z.val.val,(residual H).le_normalizer z.val.property⟩
        ((centralizer ({z.val.val} : Set G)).subgroupOf
          (normalizer (residual H : Set G))).map R.rightToCarrier =
            centralizer ({R.rightToCarrier zN} : Set R.extension.carrier) ∧
        Nonempty (centralizer ({z.val.val} : Set G) ≃*
          centralizer ({R.rightToCarrier zN} : Set R.extension.carrier))) ∧
      ∃ (t : Model m) (v : normalizer (L : Set G)),
      IsShortRootInvolution t ∧ t ∈ radical m .linear ∧
      v.val ∈ L.pCoreIn 2 ∧ orderOf v.val = 2 ∧
      R.leftToCarrier v = R.extension.baseHom t ∧
      ((centralizer ({v.val} : Set G)).subgroupOf (normalizer (L : Set G))).map
        R.leftToCarrier = centralizer ({R.extension.baseHom t} : Set R.extension.carrier) ∧
      Nonempty (((centralizer ({v.val} : Set G)).subgroupOf (normalizer (L : Set G))) ≃*
        centralizer ({R.extension.baseHom t} : Set R.extension.carrier)) ∧
      3 ∣ Nat.card (solvableResidual (centralizer ({v.val} : Set G))) ∧
      ∀ z ∈ (center (residual H)).map (residual H).subtype,
        orderOf z = 2 → ¬ IsConj z v.val := by
  exact d.ree_full_extension_short_centralizers
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
