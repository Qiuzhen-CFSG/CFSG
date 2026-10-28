module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AdditionalFusion.Tables
public import Theory.GroupTheory.InvolutionTransfer

/-!
# Involution reduction to Held's elementary subgroup S

Every involution in the finite simple ambient group is conjugate to an element
of the displayed S. Inside the model Sylow group D, the elements fixing letter
8 form a subgroup of order 64. Thompson transfer puts each involution into
its ambient image, of index two in the actual ambient Sylow group. The concrete
normal forms then conjugate it into S. This proves the reduction independently
of all later fusion and normalizer arguments.

The existing local class table reduces the nonidentity elements of S to
pi, mu, tau, lambda and pi*lambda. Every finite check uses kernel reduction
on local coordinates; the ambient group is never enumerated or identified.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.2, p.226, and Section 1, p.225.
-/

open Subgroup Equiv
open scoped Pointwise
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
open Coordinates Fusion

private def fixesEight : Subgroup H where
  carrier := {x | x.1.1 8 = 8}
  one_mem' := rfl
  mul_mem' {x y} hx hy := by
    change x.1.1 (y.1.1 8) = 8
    rw [hy, hx]
  inv_mem' {x} hx := by
    change x.1.1.symm 8 = 8
    exact x.1.1.symm_apply_eq.mpr hx.symm

private def evenD : Subgroup H := modelD ⊓ fixesEight

private theorem word_mem_evenD (a : Code) :
    word a ∈ evenD ↔ a.2.2.2.1 = 0 ∧ a.1.2.2.2 = 0 := by
  change word a ∈ modelD ∧ (word a).1.1 8 = 8 ↔ _
  rw [word_mem_modelD]
  have h : ∀ a : Code, (word a).1.1 8 = 8 ↔ a.1.2.2.2 = 0 := by decide +kernel
  rw [h]

private theorem evenD_card : Nat.card evenD = 64 := by
  rw [← Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective word word_bijective)
    (fun a => (word_mem_evenD a).symm))]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem evenD_involution_table : ∀ a : Code,
    a.2.2.2.1 = 0 → a.1.2.2.2 = 0 → word a ^ 2 = 1 →
    ∃ b : ActorCode, ∃ c : BaseCode,
      actorWord b * word a * (actorWord b)⁻¹ = elementaryWord 1 c := by
  decide +kernel

private theorem evenD_involution_isConj {x : H} (hx : x ∈ evenD) (hx2 : x ^ 2 = 1) :
    ∃ c : BaseCode, IsConj x (elementaryWord 1 c) := by
  obtain ⟨a, rfl⟩ := word_bijective.surjective x
  obtain ⟨hr, hx⟩ := (word_mem_evenD a).mp hx
  obtain ⟨b, c, hc⟩ := evenD_involution_table a hr hx hx2
  exact ⟨c, isConj_iff.mpr ⟨actorWord b, hc⟩⟩

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

private theorem sylow_involution_reduction [IsSimpleGroup G]
    (x : ambientSylow D e) (hx : orderOf x = 2) :
    ∃ c : BaseCode, IsConj (x : G) (D.a10ModelEmbedding e (elementaryWord 1 c)) := by
  let f := D.a10ModelEmbedding e
  let E : Subgroup G := evenD.map f
  have hE : E ≤ ambientSylow D e := map_mono inf_le_left
  let U : Subgroup (ambientSylow D e) := E.subgroupOf (ambientSylow D e)
  have hcard : Nat.card U = 64 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hE).toEquiv,
      card_map_of_injective (D.a10ModelEmbedding_injective e), evenD_card]
  have hindex : U.index = 2 := by
    have h := U.card_mul_index
    rw [hcard] at h
    have hs : Nat.card (ambientSylow D e) = 128 := ambientD_card D e
    rw [hs] at h
    omega
  obtain ⟨y, hxy, hy⟩ := (ambientSylow D e).exists_isConj_mem_of_index_two
    (fun K _ => D.no_index_two K) U hindex x hx
  change (y : G) ∈ E at hy
  obtain ⟨t, ht, he⟩ := hy
  change f t = (y : G) at he
  have ht2 : t ^ 2 = 1 := by
    apply D.a10ModelEmbedding_injective e
    rw [map_pow, map_one, he]
    have hyo : orderOf (y : G) = 2 := by
      obtain ⟨g, hg⟩ := isConj_iff.mp hxy
      have ho : orderOf (x : G) = orderOf (y : G) := by
        rw [← hg]
        exact ((MulAut.conj g).orderOf_eq (x : G)).symm
      rw [← ho, Subgroup.orderOf_coe, hx]
    simpa only [hyo] using pow_orderOf_eq_one (y : G)
  obtain ⟨c, hc⟩ := evenD_involution_isConj ht ht2
  refine ⟨c, hxy.trans ?_⟩
  simpa only [he] using f.map_isConj hc

/-- Held 2.2: every ambient involution is conjugate to an element of S. -/
public theorem section22_involution_isConj_word [IsSimpleGroup G] (x : G) (hx : orderOf x = 2) :
    ∃ c : BaseCode, IsConj x (D.a10ModelEmbedding e (elementaryWord 1 c)) := by
  have hp : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using hx)
  obtain ⟨T, hT⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T (ambientSylow D e)
  have hy : (MulAut.conj g) x ∈ ambientSylow D e := by
    rw [← hg]
    change (MulAut.conj g) • x ∈ (MulAut.conj g) • (T : Set G)
    exact Set.smul_mem_smul_set (hT (mem_zpowers x))
  let y : ambientSylow D e := ⟨(MulAut.conj g) x, hy⟩
  have hyo : orderOf y = 2 := by
    rw [← Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx]
  obtain ⟨c, hc⟩ := sylow_involution_reduction D e y hyo
  exact ⟨c, (isConj_iff.mpr ⟨g, rfl⟩).trans hc⟩

/-- The five local representatives suffice for every ambient involution. -/
public theorem section22_involution_representative [IsSimpleGroup G] (x : G) (hx : orderOf x = 2) :
    IsConj x D.z ∨ IsConj x (D.a10ModelEmbedding e Coordinates.mu) ∨
      IsConj x (D.a10ModelEmbedding e tau) ∨
      IsConj x (D.a10ModelEmbedding e lam) ∨
      IsConj x (D.a10ModelEmbedding e (Coordinates.pi * lam)) := by
  obtain ⟨c, hc⟩ := section22_involution_isConj_word D e x hx
  have hf := hc.trans ((D.a10ModelEmbedding e).map_isConj
    (elementaryWord_isConj 1 c).symm)
  have hb : (elementaryClass 1 c).val < 6 := by
    have h : ∀ c : BaseCode, (elementaryClass 1 c).val < 6 := by decide +kernel
    exact h c
  generalize elementaryClass 1 c = i at hf hb
  have hne : x ≠ 1 := by intro h; simp [h] at hx
  fin_cases i
  · exact (hne (isConj_one_left.mp (by simpa [localRepresentative] using hf))).elim
  · exact Or.inl (by simpa [localRepresentative, D.a10ModelEmbedding_central e] using hf)
  · exact Or.inr (Or.inl hf)
  · exact Or.inr (Or.inr (Or.inl hf))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hf)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hf)))
  all_goals norm_num at hb

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion
