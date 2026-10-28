module
public import CFSG.Quasithin.ChapterF.Section01.RankOneSmallTwoPart
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.PrimeActors
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage
public import Theory.GroupTheory.PResidual.NormalPGroupSupplement

/-!
# Proper rank-one local subgroups of Rudvalis

The native odd-index maximal-subgroup cover and the actual quotient maps to
GL₃(2) and S₅ force every proper Sylow-overgroup section modulo its intrinsic
two-core to have order dividing 840. A nonsolvable source rank-one model is
then PSL₂(4): the other small-two-part possibility PSL₂(8) has a factor nine.

The containing component supplies perfection and trivial two-core; the
proved native coverage calculations discharge the model-cover premise.
This feeds the original smaller-changed-Sylow application in Chapter6.
Source: Aschbacher–Smith A.3.12(20), F.1.1 and5.2.2,
printed pp.47–48,259 and648–649 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.RudvalisLocal
open Rudvalis

/-- The native two-core and radical-normalizer calculations discharge the
full odd-index maximal-subgroup cover on the literal containing model. -/
theorem sylow_overgroup_cover (hO : pCore 2 Model = ⊥) :
    SylowOvergroups.OddIndexMaximalCover :=
  SylowOvergroups.oddIndexMaximalCover_of_twoCore_of_radicalCover hO
    Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.rudvalis_oddIndexMaximalTwoCore
    SylowOvergroups.oddIndexMaximalRadicalCover

/-- A proper nonsolvable subgroup normalized by a full Sylow of Rudvalis has
PSL₂(4) as its two-core quotient whenever that quotient is a source rank-one model. -/
theorem rankOne_quotient_four [Group.IsPerfect Model]
    (hO : pCore 2 Model = ⊥)
    (S : Sylow 2 Model) (B : Subgroup Model)
    (hne : B ≠ ⊤) (hns : ¬ Group.IsSolvable B)
    (hn : (S : Subgroup Model) ≤ normalizer (B : Set Model))
    (hm : IsRankOneModel (B ⧸ pCore 2 B)) :
    ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4 := by
  have hJ : B ⊔ (S : Subgroup Model) ≠ ⊤ := by
    intro he
    let : B.Normal := normalizer_eq_top_iff.mp (top_unique (he ▸ sup_le B.le_normalizer hn))
    let : Nontrivial (Model ⧸ B) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (Model ⧸ B) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective B)
    let : Group.IsNilpotent (Model ⧸ B) :=
      (isPGroup_quotient_of_sup_eq_top B (S : Subgroup Model) S.isPGroup' he).isNilpotent
    exact Group.IsPerfect.not_isSolvable (Model ⧸ B) inferInstance
  have hd := SylowOvergroups.proper_overgroup_section_order (sylow_overgroup_cover hO) S
    (B ⊔ (S : Subgroup Model)) B le_sup_right hJ le_sup_left
  have hquot : ¬ Group.IsSolvable (B ⧸ pCore 2 B) := by
    intro hs
    let := hs
    let : Group.IsNilpotent (pCore 2 B) := pCore_isNilpotent
    exact hns (Group.isSolvable_of_ker_le_range (pCore 2 B).subtype
      (QuotientGroup.mk' (pCore 2 B)) (by simp))
  obtain ⟨f,hf,hf3,hfmodel⟩ := hm.binary_of_small_twoPart hquot
    (fun h16 => (by decide : ¬ 16 ∣ 840) (h16.trans hd))
  have hf2 : f = 2 := by
    by_contra hne2
    have hf3 : f = 3 := by omega
    subst f
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hfmodel
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (f := 3) (by
      simpa only [Nat.card_eq_fintype_card] using hF)
    have hc := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
    rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
      (CharTwo.neg_eq 1),mul_one,hF,←Nat.card_congr e.toEquiv] at hc
    rw [hc] at hd
    norm_num at hd
  subst f
  exact hfmodel
end CFSG.Quasithin.ChapterF.Source.RudvalisLocal
