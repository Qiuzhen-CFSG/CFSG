module
public import CFSG.Quasithin.ChapterF.Section01.RankOneSmallTwoPart
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.PrimeActors
public import Theory.GroupTheory.PResidual.NormalPGroupSupplement

/-!
# Proper rank-one local subgroups of Higman–Sims

The two native full-Sylow overgroups map to S₅ and GL₃(2) with two-group
kernels. Every subgroup section modulo its intrinsic two-core therefore
has order dividing 840. The source rank-one models of two-part at most
eight are PSL₂(4) and PSL₂(8); the latter has order divisible by nine.
Perfection of the containing carrier is inherited from the original
C-component and makes the Sylow join proper.

This supplies the actual smaller-changed-Sylow application in Chapter6.
Source: Aschbacher–Smith A.3.12(18), F.1.1 and5.2.2,
printed pp.47–48,259 and648–649 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.HigmanSimsLocal
open Sporadic.LeechRelated.HS

/-- A proper nonsolvable subgroup normalized by a full Sylow of HS has
PSL₂(4) as its two-core quotient whenever that quotient is a source rank-one model. -/
theorem rankOne_quotient_four [Group.IsPerfect Carrier]
    (S : Sylow 2 Carrier) (B : Subgroup Carrier)
    (hne : B ≠ ⊤) (hns : ¬ Group.IsSolvable B)
    (hn : (S : Subgroup Carrier) ≤ normalizer (B : Set Carrier))
    (hm : IsRankOneModel (B ⧸ pCore 2 B)) :
    ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4 := by
  have hJ : B ⊔ (S : Subgroup Carrier) ≠ ⊤ := by
    intro he
    let : B.Normal := normalizer_eq_top_iff.mp (top_unique (he ▸ sup_le B.le_normalizer hn))
    let : Nontrivial (Carrier ⧸ B) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (Carrier ⧸ B) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective B)
    let : Group.IsNilpotent (Carrier ⧸ B) :=
      (isPGroup_quotient_of_sup_eq_top B (S : Subgroup Carrier) S.isPGroup' he).isNilpotent
    exact Group.IsPerfect.not_isSolvable (Carrier ⧸ B) inferInstance
  have hd := SylowOvergroups.proper_overgroup_section_order S
    (B ⊔ (S : Subgroup Carrier)) B le_sup_right hJ le_sup_left
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
end CFSG.Quasithin.ChapterF.Source.HigmanSimsLocal
