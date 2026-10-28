module
public import Theory.GroupTheory.Amalgam.ParabolicRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceIncidence
public import BenderSuzuki.MatrixGroups.SuzukiZero
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# The source local data for the binary Ree recognition branch

The literal common Sylow subgroup has order4096 and is self-normalizing in
both endpoints. The quotient models are the actual Sz(2) and S3 groups.
These inputs construct all six original F.1.1 hypotheses and identify both
source Borels with the common Sylow subgroup. Consequently the endpoint
intersection is precisely that subgroup, and the inclusion amalgam is Sylow
embedded and faithful. Sylow multiplicities give the exact core and endpoint
orders1024/20480 and2048/12288.

This is the source-input package used in J.4.5 before local recognition.
It does not assert that the endpoint groups are isomorphic to the binary Ree
parabolics. That independent recognition implication still requires proof.

Source: Aschbacher–Smith F.1.1, F.1.3(6), F.1.12(I)(5), and J.4.5,
printed pp.259–263 and441–442.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.BinaryRee
variable {H:Type*} [Group H] [Finite H]

private theorem core_card_of_sylow_quotient (P:Sylow 2 H) (hP:Nat.card P=4096)
    (m:ℕ) (hm:m=20 ∨ m=6) (hq:Nat.card (H⧸pCore 2 H)=m) :
    (m=20 → Nat.card (pCore 2 H)=1024 ∧ Nat.card H=20480) ∧
    (m=6 → Nat.card (pCore 2 H)=2048 ∧ Nat.card H=12288) := by
  obtain ⟨n,hn⟩:=(pCore_isPGroup (p:=2) (G:=H)).exists_card_eq
  have hcard:=card_eq_card_quotient_mul_card_subgroup (pCore 2 H)
  rw [hq,hn] at hcard
  have hpow:=P.card_eq_multiplicity
  rw [hP,hcard,Nat.factorization_mul (by rcases hm with rfl|rfl <;>decide) (by positivity),
    Nat.factorization_pow] at hpow
  constructor
  · intro hm20
    rw [hm20] at hpow hcard
    have hf20:Nat.factorization 20 2=2:=by decide +kernel
    simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,Nat.Prime.factorization_self (by decide:Nat.Prime 2),hf20,mul_one] at hpow
    have he:12=2+n:=by
      apply Nat.pow_right_injective (by decide : 1<2)
      simpa using hpow
    have hn10:n=10:=by omega
    subst n
    constructor
    · simpa using hn
    · simpa using hcard
  · intro hm6
    rw [hm6] at hpow hcard
    have hf6:Nat.factorization 6 2=1:=by decide +kernel
    simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul,Nat.Prime.factorization_self (by decide:Nat.Prime 2),hf6,mul_one] at hpow
    have he:12=1+n:=by
      apply Nat.pow_right_injective (by decide : 1<2)
      simpa using hpow
    have hn11:n=11:=by omega
    subst n
    constructor
    · simpa using hn
    · simpa using hcard

variable {G:Type*} [Group G] [Finite G]

structure LocalData (P₁ T P₂:Subgroup G) : Prop where
  le_left:T≤P₁
  le_right:T≤P₂
  sylow_left:∃P:Sylow 2 P₁,(P:Subgroup P₁)=T.subgroupOf P₁
  sylow_right:∃P:Sylow 2 P₂,(P:Subgroup P₂)=T.subgroupOf P₂
  normalizer_left:normalizer (T.subgroupOf P₁:Set P₁)=T.subgroupOf P₁
  normalizer_right:normalizer (T.subgroupOf P₂:Set P₂)=T.subgroupOf P₂
  quotient_left:Nonempty ((P₁⧸pCore 2 P₁)≃*BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)
  quotient_right:Nonempty ((P₂⧸pCore 2 P₂)≃*Equiv.Perm (Fin 3))
  characteristic_left:Theory.GroupTheory.generalizedFitting P₁=pCore 2 P₁
  characteristic_right:Theory.GroupTheory.generalizedFitting P₂=pCore 2 P₂
  core_free:pCore 2 (P₁⊔P₂:Subgroup G)=⊥
  card_overlap:Nat.card T=4096

omit [Finite G] in
private theorem borel_eq_of_self_normalizer {P T:Subgroup G} (hTP:T≤P)
    (hN:normalizer (T.subgroupOf P:Set P)=T.subgroupOf P) : borel P T=T := by
  rw [←subgroupOf_normalizer_eq hTP] at hN
  rw [borel,inf_eq_left.mpr hTP]
  ext g
  constructor
  · rintro ⟨hg,hgN⟩
    exact (show (⟨g,hg⟩:P)∈T.subgroupOf P from hN ▸ hgN)
  · intro hg
    exact ⟨hTP hg,T.le_normalizer hg⟩

namespace LocalData
variable {P₁ T P₂:Subgroup G} (h:LocalData P₁ T P₂)
include h

omit [Finite G] in
theorem borels : borel P₁ T=T ∧ borel P₂ T=T :=
  ⟨borel_eq_of_self_normalizer h.le_left h.normalizer_left,
    borel_eq_of_self_normalizer h.le_right h.normalizer_right⟩

omit [Finite G] in
theorem commonBorel_eq : commonBorel ![P₁,P₂] T=T := by
  change borel P₁ T⊔borel P₂ T⊔T=T
  rw [h.borels.1,h.borels.2,sup_idem,sup_idem]

omit [Finite G] in
theorem parabolic_eq (i:Fin 2):parabolic ![P₁,P₂] T i=![P₁,P₂] i := by
  rw [parabolic_eq_sup_commonBorel,h.commonBorel_eq]
  fin_cases i
  · exact sup_eq_left.mpr h.le_left
  · exact sup_eq_left.mpr h.le_right

theorem source_hypothesis : HypothesisF11 ![P₁,P₂] T := by
  have hmap {P:Subgroup G} (hTP:T≤P) (S:Sylow 2 P) (hS:(S:Subgroup P)=T.subgroupOf P) :
      (S:Subgroup P).map P.subtype=T := by rw [hS,subgroupOf_map_subtype,inf_eq_left.mpr hTP]
  refine {
    finite_S := inferInstance
    S_isP := ?_
    S_normalizes := ?_
    sylow := ?_
    quotient := ?_
    cross := ?_
    twoCore_free := ?_
    characteristic_two := ?_ }
  · obtain ⟨S,hS⟩:=h.sylow_left
    rw [←hmap h.le_left S hS]
    exact S.isPGroup'.map P₁.subtype
  · intro i
    fin_cases i
    · exact h.le_left.trans P₁.le_normalizer
    · exact h.le_right.trans P₂.le_normalizer
  · intro i
    fin_cases i
    · obtain ⟨S,hS⟩:=h.sylow_left
      refine ⟨S,?_⟩
      change (S:Subgroup P₁).map P₁.subtype=T⊓P₁
      rw [hmap h.le_left S hS,inf_eq_left.mpr h.le_left]
    · obtain ⟨S,hS⟩:=h.sylow_right
      refine ⟨S,?_⟩
      change (S:Subgroup P₂).map P₂.subtype=T⊓P₂
      rw [hmap h.le_right S hS,inf_eq_left.mpr h.le_right]
  · intro i
    fin_cases i
    · exact .suzuki 0 h.quotient_left
    · obtain ⟨e⟩:=h.quotient_right
      obtain ⟨f⟩:=BenderSuzuki.External.huppert_II_6_14_a_psl2_card_two
        (K:=ZMod 2) (by simp)
      exact .linear 1 (by decide) ⟨ZMod 2,inferInstance,inferInstance,by simp,⟨e.trans f.symm⟩⟩
  · intro i
    fin_cases i
    · change borel P₂ T≤normalizer P₁
      rw [h.borels.2]
      exact h.le_left.trans P₁.le_normalizer
    · change borel P₁ T≤normalizer P₂
      rw [h.borels.1]
      exact h.le_right.trans P₂.le_normalizer
  · change pCore 2 ((P₁⊔P₂)⊔T:Subgroup G)=⊥
    rw [sup_eq_left.mpr (h.le_left.trans le_sup_left)]
    exact h.core_free
  · intro i
    rw [h.parabolic_eq]
    fin_cases i
    · exact h.characteristic_left
    · exact h.characteristic_right

theorem orders : Nat.card (pCore 2 P₁)=1024 ∧ Nat.card P₁=20480 ∧
    Nat.card (pCore 2 P₂)=2048 ∧ Nat.card P₂=12288 := by
  have hcard {P:Subgroup G} (hTP:T≤P) (S:Sylow 2 P) (hS:(S:Subgroup P)=T.subgroupOf P):
      Nat.card S=4096 := by
    rw [hS,Nat.card_congr (subgroupOfEquivOfLe hTP).toEquiv,h.card_overlap]
  obtain ⟨S₁,hS₁⟩:=h.sylow_left
  obtain ⟨S₂,hS₂⟩:=h.sylow_right
  obtain ⟨e₁⟩:=h.quotient_left
  obtain ⟨e₂⟩:=h.quotient_right
  have hq₁:Nat.card (P₁⧸pCore 2 P₁)=20:=
    (Nat.card_congr e₁.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card
  have hq₂:Nat.card (P₂⧸pCore 2 P₂)=6:=by
    rw [Nat.card_congr e₂.toEquiv,Nat.card_eq_fintype_card]
    decide
  have h₁:=(core_card_of_sylow_quotient S₁ (hcard h.le_left S₁ hS₁) 20 (Or.inl rfl) hq₁).1 rfl
  have h₂:=(core_card_of_sylow_quotient S₂ (hcard h.le_right S₂ hS₂) 6 (Or.inr rfl) hq₂).2 rfl
  exact ⟨h₁.1,h₁.2,h₂.1,h₂.2⟩

theorem intersection : P₁⊓P₂=T := by
  have hh:=lemma_F_1_3_6 h.source_hypothesis
  rw [h.parabolic_eq 0,h.parabolic_eq 1,h.commonBorel_eq] at hh
  exact hh

theorem faithful : Theory.GroupTheory.RankTwoAmalgam.Faithful
    (Theory.GroupTheory.RankTwoAmalgam.ofSubgroups P₁ T P₂ h.le_left h.le_right) :=
  Theory.GroupTheory.RankTwoAmalgam.faithful_ofSubgroups_of_pCore_eq_bot P₁ T P₂
    h.le_left h.le_right h.source_hypothesis.S_isP h.core_free

omit [Finite G] in
theorem sylow_embedded : Theory.GroupTheory.RankTwoAmalgam.SylowEmbedded 2
    (Theory.GroupTheory.RankTwoAmalgam.ofSubgroups P₁ T P₂ h.le_left h.le_right) where
  left_injective:=inclusion_injective h.le_left
  right_injective:=inclusion_injective h.le_right
  left_sylow:=by
    obtain ⟨P,hP⟩:=h.sylow_left
    exact ⟨P,hP.trans (inclusion_range h.le_left).symm⟩
  right_sylow:=by
    obtain ⟨P,hP⟩:=h.sylow_right
    exact ⟨P,hP.trans (inclusion_range h.le_right).symm⟩

theorem local_rank_one_data (i:Fin 2) : Nonempty (LocalRankOneData (![P₁,P₂] i) T) := by
  have hTP:T≤![P₁,P₂] i:=by fin_cases i;exact h.le_left;exact h.le_right
  obtain ⟨S,hS⟩:=h.source_hypothesis.sylow i
  have hB:borel (![P₁,P₂] i) T=T:=by fin_cases i;exact h.borels.1;exact h.borels.2
  refine ⟨{
    finite_P:=inferInstance
    Pstar:=![P₁,P₂] i
    Pstar_le:=le_rfl
    normal:=by rw [subgroupOf_self];infer_instance
    same_core:=rfl
    supplement:=sup_eq_left.mpr hTP
    characteristic_two:=?_
    sylow:=S
    borel_eq:=?_
    quotient:=h.source_hypothesis.quotient i }⟩
  · have hh:=h.source_hypothesis.characteristic_two i
    rw [h.parabolic_eq] at hh
    exact hh
  · rw [hS,inf_eq_left.mpr hTP,inf_eq_right.mpr hTP]
    simpa only [borel,inf_eq_left.mpr hTP] using hB.symm

theorem locally_rank_one_triple (hgen:P₁⊔P₂=⊤) : LocallyRankOneTriple ![P₁,P₂] T := by
  refine ⟨hgen,h.intersection,?_,h.local_rank_one_data⟩
  intro N hN hNT
  have hNp:IsPGroup 2 N:=h.source_hypothesis.S_isP.of_injective
    (inclusion hNT) (inclusion_injective hNT)
  have hNcore:N≤pCore 2 G:=le_sSup ⟨hN,hNp⟩
  let e:(P₁⊔P₂:Subgroup G)≃*G:=(MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  have hcore:pCore 2 G=⊥:=by
    rw [←pCore_map_iso 2 e,h.core_free,Subgroup.map_bot]
  exact le_bot_iff.mp (hNcore.trans_eq hcore)

end LocalData

end CFSG.Quasithin.ChapterF.Source.BinaryRee
