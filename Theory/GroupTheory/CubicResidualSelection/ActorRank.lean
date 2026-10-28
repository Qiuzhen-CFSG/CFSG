module
public import Theory.GroupTheory.CubicResidualSelection
public import Theory.GroupTheory.SymmetricThreeResidualNormality
public import Theory.GroupTheory.SymmetricThreeResidualRank
public import Theory.Quasithin.CoprimeRank

/-!
# Rank of an actor beside a centralizing Thompson factor

Let K and I be normal in H. A cubic O²(K)/O₂(O²(K)), centralized by I,
and the three-perfectness of I select I/O₂(I)≅S₃. A Sylow-stable actor A
has a normal two-perfect lift of its intersection with this S₃'s odd
residual. If every such lift lies in K, the kernel intersection theorem
kills it modulo O₂(H). The independent cubic then bounds m₃(A) by one.

The proof uses H/O₂(H), whose kernel is a two-group, even when the
original action kernel K is larger. The source application uses A=L₁
and the actual earlier 13.3.9 classification to supply the lift bound.
Source: Aschbacher–Smith 13.4.8, printed p.905.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.CubicResidualSelection
variable {H : Type*} [Group H] [Finite H]
local notation "S3" => Equiv.Perm (Fin 3)

/-- A Sylow-stable two-perfect actor has cubic rank at most one when its
normal two-perfect subgroups lie in the centralizing kernel. -/
theorem actor_rank_le_one (K I A : Subgroup H) [K.Normal] [I.Normal]
    (hQK : pCore 2 H ≤ K)
    (hcard : let D := (pResidual 2 K).map K.subtype
      Nat.card (D ⧸ pCore 2 D) = 3)
    (hI : IsPPerfect 3 I)
    (hIC : let D := (pResidual 2 K).map K.subtype
      ⁅I,D⁆ ≤ D.pCoreIn 2)
    (hm : Nonempty ((I.map (QuotientGroup.mk' K)) ≃* S3) ∨
      Nonempty ((I.map (QuotientGroup.mk' K)) ≃* (S3 × S3)))
    (hrank : primeRank 3 H ≤ 2)
    (S : Sylow 2 H) (hSA : (S : Subgroup H) ≤ normalizer (A : Set H))
    (hA : IsPPerfect 2 A)
    (horder : ∃ m n : ℕ, Nat.card A ∣ 2 ^ m * 3 ^ n)
    (hthree : 3 ∣ Nat.card A)
    (hclass : ∀ Y : Subgroup H, Y.Normal → IsPPerfect 2 Y → Y ≤ A → Y ≤ K) :
    primeRank 3 A ≤ 1 := by
  obtain ⟨⟨e⟩,hIK⟩ := core_quotient_single K I hQK hcard hI hIC hm hrank
  let Q := pCore 2 H
  let q := QuotientGroup.mk' Q
  let Ib := I.map q
  let Ab := A.map q
  let : Ib.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let ei : Ib ≃* S3 := (coreQuotientEquivImage 2 I).symm.trans e
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  obtain ⟨Y,hYn,hYp,hYA,hYm⟩ := SymmetricThreeCubicNormality.residual_intersection_lift
    q (QuotientGroup.mk'_surjective _) hk Ib (Or.inl ⟨ei⟩) S A hSA
  have hYK := hclass Y hYn hYp hYA
  have hYI : Y.map q ≤ Ib := by
    rw [hYm]
    exact inf_le_left.trans (map_subtype_le _)
  have hYQ : Y ≤ Q := by
    intro y hy
    obtain ⟨i,hi,hei⟩ := hYI (mem_map_of_mem q hy)
    have hdiff : y * i⁻¹ ∈ Q := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (y * i⁻¹) = 1
      rw [map_mul,map_inv,hei,mul_inv_cancel]
    have hiK : i ∈ K := by
      have hh := K.mul_mem (K.inv_mem (hQK hdiff)) (hYK hy)
      simpa only [mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one] using hh
    have hiQ := hIK ⟨hi,hiK⟩
    have hh := Q.mul_mem hdiff hiQ
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
  have hd : Disjoint ((pResidual 2 Ib).map Ib.subtype) Ab := by
    apply disjoint_iff.mpr
    rw [← hYm]
    exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']; exact hYQ)
  let f := q.subgroupMap A
  have hfk : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  have hcop : Nat.Coprime 3 (Nat.card f.ker) := by
    obtain ⟨n,hn⟩ := hfk.exists_card_eq
    rw [hn]; exact (by decide : Nat.Coprime 3 2).pow_right n
  have hne : Ab ≠ ⊥ := by
    intro he
    have hAK : A ≤ q.ker := (Subgroup.map_eq_bot_iff _).mp he
    have hp := hk.to_le hAK
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hn] at hthree
    exact (Nat.prime_three.coprime_iff_not_dvd.mp
      ((by decide : Nat.Coprime 3 2).pow_right n)) hthree
  have ho : ∃ m n : ℕ, Nat.card Ab ∣ 2 ^ m * 3 ^ n := by
    obtain ⟨m,n,hh⟩ := horder
    exact ⟨m,n,(card_map_dvd A q).trans hh⟩
  have hr := (SymmetricThreeCubicNormality.single_and_rank_of_residual_disjoint Ib Ab
    (Or.inl ⟨ei⟩) (hA.of_surjective f (q.subgroupMap_surjective A)) hne ho
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) Q pCore_isPGroup).trans hrank) hd).2
  exact (primeRank_le_of_coprime_ker 3 f hcop).trans hr
end Theory.GroupTheory.CubicResidualSelection
