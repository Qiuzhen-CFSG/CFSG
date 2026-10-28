module
public import CFSG.Quasithin.ChapterF.Section01.RankOneMathieuSections
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SylowOvergroups.PrimeActors
public import Theory.GroupTheory.PResidual.NormalPGroupSupplement

/-!
# Proper rank-one local subgroups of Hall–Janko

In a perfect J₂ carrier, a proper subgroup normalized by a full Sylow
cannot generate the whole group together with that Sylow: the resulting
quotient would be both perfect and a two-group. The certified native
Sylow-overgroup cover therefore bounds its order by 1920 or 1152.
The existing source rank-one order calculation leaves PSL₂(4) or PSL₂(8),
and the absence of seven in both local orders excludes PSL₂(8).

Perfection is inherited from the containing C-component; no independent
simplicity hypothesis is added for the model. All intrinsic two-core
kernels remain in the statement and in the Chapter6 original Cartan
application. Source: Aschbacher–Smith A.3.12(16), F.1.1 and5.2.2,
printed pp.47–48,259 and648–649 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.JankoTwoLocal
open Sporadic.LeechRelated.J2

/-- A proper nonsolvable subgroup normalized by a full Sylow of J₂ has
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
  have hd : Nat.card (B ⧸ pCore 2 B) ∣ 1920 ∨ Nat.card (B ⧸ pCore 2 B) ∣ 1152 :=
    (SylowOvergroups.proper_overgroup_order S _ le_sup_right hJ).imp
      (fun h => (card_quotient_dvd_card _).trans ((card_dvd_of_le (show B ≤ B ⊔ (S : Subgroup Carrier)
        from le_sup_left)).trans h))
      (fun h => (card_quotient_dvd_card _).trans ((card_dvd_of_le (show B ≤ B ⊔ (S : Subgroup Carrier)
        from le_sup_left)).trans h))
  have hquot : ¬ Group.IsSolvable (B ⧸ pCore 2 B) := by
    intro hs
    let := hs
    let : Group.IsNilpotent (pCore 2 B) := pCore_isNilpotent
    exact hns (Group.isSolvable_of_ker_le_range (pCore 2 B).subtype
      (QuotientGroup.mk' (pCore 2 B)) (by simp))
  have hbound : Nat.card (B ⧸ pCore 2 B) ∣ 244823040 := by
    rcases hd with h | h
    · exact h.trans (by decide)
    · exact h.trans (by decide)
  apply (hm.mathieu_section hquot hbound).resolve_right
  intro he
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (f := 3) (by
    simpa only [Nat.card_eq_fintype_card, show (2:ℕ)^3 = 8 from rfl] using hF)
  have hc := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
  rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (CharTwo.neg_eq 1),mul_one,hF,←Nat.card_congr e.toEquiv] at hc
  rw [hc] at hd
  norm_num at hd

end CFSG.Quasithin.ChapterF.Source.JankoTwoLocal
