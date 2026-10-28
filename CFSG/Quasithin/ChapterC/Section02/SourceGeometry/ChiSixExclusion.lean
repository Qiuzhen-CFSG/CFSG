module
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.TranspositionExclusion
public import CFSG.Quasithin.ChapterC.Section01.RankOne.LocalC129.ChiZeroRank
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer

/-!
# Chi, alternating-six parabolic and binary G₂ exclusions

An A₆ two-core section forces a factor of five in the actual star
intersection. The source kernel has order prime to five. Both small-part
partition stabilizers have order prime to five, while the rank-one chi
blocks have three-rank at most one. The binary derived G₂ group has no
factor of five even before taking the star quotient.

The partition argument is adapted from the private calculation in
Chapter14's ModelSieve/BlockComparisons, without an upward dependency.
Source: Aschbacher–Smith C.2.7(3)(a,e,f), pp.145–147, and 3.3.22, p.597.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Equiv Equiv.Perm
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {H K R M B : Subgroup G}

omit [Finite G] in
private theorem core_quotient_six_card
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) :
    Nat.card (B ⧸ pCore 2 B) = 360 := by
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

omit [Finite G] in
theorem five_dvd_card_of_six_quotient
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) : 5 ∣ Nat.card B := by
  have hd := card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 B))
    (QuotientGroup.mk'_surjective _)
  rw [core_quotient_six_card e] at hd
  exact (by decide : 5 ∣ 360).trans hd

theorem starM_five_dvd_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) :
    5 ∣ Nat.card (starM K R M) := by
  have hf := five_dvd_card_of_six_quotient e
  have hd : 5 ∣ Nat.card (M ⊓ K : Subgroup G) := hf.trans (card_dvd_of_le hB)
  let q := QuotientGroup.mk' (starKernel K R)
  let D := (M ⊓ K).subgroupOf (K ⊔ R)
  let f := q.comp D.subtype
  have hD : Nat.card D = Nat.card (M ⊓ K : Subgroup G) :=
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_right.trans le_sup_left)).toEquiv
  have hker : ¬5 ∣ Nat.card f.ker := by
    intro h5
    let j : f.ker →* (toStarImage K R).ker :=
      { toFun := fun x => ⟨⟨x.val.val.val,x.val.property.2⟩,Subtype.ext x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hj : Function.Injective j := by
      intro x y hh
      exact Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun a => a.val.val) hh)))
    exact toStarImage_ker_not_five_from_source h (h5.trans (card_dvd_of_injective j hj))
  have hc := f.ker.card_mul_index
  rw [index_ker, hD] at hc
  rw [←hc] at hd
  have hr : f.range = starM K R M := by
    rw [MonoidHom.range_comp,range_subtype]
    rfl
  rw [←hr]
  exact (Nat.prime_five.dvd_mul.mp hd).resolve_left hker

theorem no_chiZero_containing_six (hB : B ≤ K)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (hK : IsChiZeroBlock K) : False := by
  have hr : primeRank 3 B = 2 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 B) pCore_isPGroup,
      primeRank_equiv 3 e,
      GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 6 3 (by decide) (by decide)]
  have hb := _root_.primeRank_le_of_injective 3 (inclusion hB) (inclusion_injective hB)
  have hk := hK.threeRank_le_one
  omega

private theorem perm_eq_one_of_pow_five {α : Type*} [Finite α]
    (hc : Nat.card α ≤ 4) (q : Equiv.Perm α) (hq : q ^ 5 = 1) : q = 1 := by
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 5 24)
    (orderOf_dvd_of_pow_eq_one hq)
  apply (orderOf_dvd_natCard q).trans
  rw [Nat.card_perm]
  exact Nat.factorial_dvd_factorial hc

/-- A five-element fixes both the set of small parts and every point in each part. -/
theorem partition_not_five_dvd_card {n k : ℕ} {sizes : Fin k → ℕ}
    (p : Partition n k sizes) (hk : k ≤ 4) (hs : ∀ i, sizes i ≤ 4) :
    ¬ 5 ∣ Nat.card p.stabilizer := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro hd
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 5 hd
  have hqpow : q ^ 5 = 1 := hq ▸ pow_orderOf_eq_one q
  let : MulAction p.stabilizer (Set.range p.part) :=
    inferInstanceAs (MulAction (MulAction.stabilizer (Equiv.Perm (Fin n))
      (Set.range p.part)) (Set.range p.part))
  let ρ := MulAction.toPermHom p.stabilizer (Set.range p.part)
  have hρ : ρ q = 1 := perm_eq_one_of_pow_five
    ((Finite.card_range_le p.part).trans (by simpa using hk)) _ (by
      rw [← map_pow, hqpow, map_one])
  have hparts : ∀ i, (q : Equiv.Perm (Fin n)) • p.part i = p.part i := by
    intro i
    exact congrArg Subtype.val (Equiv.congr_fun hρ ⟨p.part i, ⟨i, rfl⟩⟩)
  have hpoint : ∀ i (x : Fin n), x ∈ p.part i → (q : Equiv.Perm (Fin n)) x = x := by
    intro i x hx
    have hinv : ∀ x, (q : Equiv.Perm (Fin n)) x ∈ p.part i ↔ x ∈ p.part i := by
      intro x
      conv_lhs => rw [← hparts i]
      exact Finset.smul_mem_smul_finset_iff (q : Equiv.Perm (Fin n))
    let σ : Equiv.Perm (p.part i) := (q : Equiv.Perm (Fin n)).subtypePerm hinv
    have hσpow : σ ^ 5 = 1 := by
      apply Equiv.ext
      intro a
      apply Subtype.ext
      change (((q : Equiv.Perm (Fin n)).subtypePerm hinv ^ 5) a : Fin n) = a
      rw [subtypePerm_apply_pow_of_mem]
      have hh : (q : Equiv.Perm (Fin n)) ^ 5 = 1 := congrArg Subtype.val hqpow
      rw [hh]
      rfl
    have hσ : σ = 1 := perm_eq_one_of_pow_five (by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, p.card]
      exact hs i) _ hσpow
    exact congrArg Subtype.val (Equiv.congr_fun hσ ⟨x, hx⟩)
  have hone : q = 1 := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    obtain ⟨i, hi⟩ := p.cover x
    exact hpoint i x hi
  rw [hone, orderOf_one] at hq
  norm_num at hq

private theorem no_small_partition_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) (e6 : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    {n k : ℕ} {sizes : Fin k → ℕ} (p : Partition n k sizes)
    (hk : k ≤ 4) (hs : ∀ i, sizes i ≤ 4)
    (e : StarQuotient K R ≃* Equiv.Perm (Fin n))
    (hm : (starM K R M).map e.toMonoidHom = alternatingGroup (Fin n) ⊓ p.stabilizer) :
    False := by
  have hd := starM_five_dvd_of_six h hB e6
  rw [←card_map_of_injective (K := starM K R M) (f := e.toMonoidHom) e.injective,hm] at hd
  exact partition_not_five_dvd_card p hk hs (hd.trans (card_dvd_of_le inf_le_right))

/-- All four actual chi alternatives exclude an embedded A6 two-core section. -/
theorem no_chi_alternative_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) (e6 : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (hc : ChiAlternative K R M) : False := by
  cases hc with
  | binary n hb _ _ => exact no_chiZero_containing_six (hB.trans inf_le_right) e6 (Or.inl ⟨n,hb⟩)
  | five hb _ _ _ => exact no_chiZero_containing_six (hB.trans inf_le_right) e6 (Or.inr (Or.inr hb))
  | sevenDihedral _ _ he =>
    obtain ⟨e,d,hd⟩ := he
    exact no_small_partition_of_six h hB e6 d (by decide)
      (by intro i; fin_cases i <;> norm_num) e.groupIso hd
  | sevenElementary _ _ he =>
    obtain ⟨e,d,hd⟩ := he
    exact no_small_partition_of_six h hB e6 d (by decide)
      (by intro i; fin_cases i <;> norm_num) e.groupIso hd

/-- Both actual alternating-six parabolics have order prime to five. -/
theorem a6Parabolic_not_five_dvd {A : Type*} [Group A] [Finite A]
    {P : Subgroup A} (hP : IsA6MaximalParabolic P) : ¬ 5 ∣ Nat.card P := by
  obtain ⟨e, hP⟩ := hP
  have hc : Nat.card ((P.map e.toMonoidHom).map (alternatingGroup (Fin 6)).subtype) =
      Nat.card P := by
    rw [Subgroup.card_map_of_injective (alternatingGroup (Fin 6)).subtype_injective,
      Subgroup.card_map_of_injective e.injective]
  intro h5
  rcases hP with ⟨d, hd⟩ | ⟨d, hd⟩
  · rw [hd] at hc
    exact partition_not_five_dvd_card d (by decide)
      (by intro i; fin_cases i <;> norm_num)
      ((hc.symm ▸ h5).trans (Subgroup.card_dvd_of_le inf_le_right))
  · rw [hd] at hc
    exact partition_not_five_dvd_card d (by decide)
      (by intro i; fin_cases i <;> norm_num)
      ((hc.symm ▸ h5).trans (Subgroup.card_dvd_of_le inf_le_right))

theorem no_six_parabolic_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (hp : IsA6MaximalParabolic ((starM K R M).subgroupOf (starImage K R K))) : False := by
  apply a6Parabolic_not_five_dvd hp
  rw [Nat.card_congr (subgroupOfEquivOfLe (starM_le K R M)).toEquiv]
  exact starM_five_dvd_of_six h hB e

/-- The actual derived binary G2 carrier has no factor of five. -/
theorem no_binaryG2_containing_six (hB : B ≤ K)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    (hm : IsG2TwoBlock K) : False := by
  have hd := (five_dvd_card_of_six_quotient e).trans (card_dvd_of_le hB)
  obtain ⟨eK⟩ := hm.quotient_model
  obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
  rw [←(pCore 2 K).card_mul_index,hk,index_eq_card,
    Nat.card_congr eK.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
  have hh := ((by decide : Nat.Coprime 5 2).pow_right k).dvd_of_dvd_mul_left hd
  norm_num at hh
end CFSG.Quasithin.ChapterC.C27Source
