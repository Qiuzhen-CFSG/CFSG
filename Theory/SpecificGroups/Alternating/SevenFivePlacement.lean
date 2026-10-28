module
public import Theory.SpecificGroups.AlternatingSix.SmallIndex
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# A₅ subgroups normalized by a full Sylow two-subgroup of A₇

A faithful seven-letter A₅ action has one nontrivial orbit, of size five or
six. In the latter case its normalizer fixes the remaining letter. A full
Sylow two-subgroup would make this a subgroup of index at most three in A₆,
contradicting simplicity. Thus the original subgroup is the alternating
pointwise stabilizer of two letters. Its two-subgroups fix three letters and
centralize the three-cycle on those letters.

Source: Aschbacher–Smith, C.5.13, printed pp.162–163, the restriction step
matching the two A₅ block types with the two A₇ module alternatives.
-/

public section
open Subgroup MulAction
namespace Theory.SpecificGroups.Alternating.SevenFivePlacement
local notation "A7" => alternatingGroup (Fin 7)

private theorem orbit_card {H : Type*} [Group H] [Finite H] [IsSimpleGroup H]
    [MulAction H (Fin 7)] (hH : Nat.card H = 60) (i : Fin 7) :
    (orbit H i).ncard = 1 ∨ (orbit H i).ncard = 5 ∨ (orbit H i).ncard = 6 := by
  have hd : (orbit H i).ncard ∣ 60 := by
    rw [← index_stabilizer, ← hH]
    exact (stabilizer H i).index_dvd_card
  have hb : (orbit H i).ncard ≤ 7 := by
    simpa using Set.ncard_le_ncard (Set.subset_univ (orbit H i))
  have hn : (orbit H i).ncard ≠ 0 := Set.ncard_ne_zero_of_mem (mem_orbit_self i)
  have hsmall : (orbit H i).ncard ≤ 4 → (orbit H i).ncard = 1 := by
    intro h
    have ht : stabilizer H i = ⊤ :=
      Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt _ (by
        rw [index_stabilizer, hH]
        have hf := Nat.factorial_le h
        norm_num [Nat.factorial] at hf ⊢
        omega)
    rw [← index_stabilizer, ht, index_top]
  interval_cases hc : (orbit H i).ncard <;> simp_all

private theorem fixed_card (B : Subgroup A7) (e : B ≃* alternatingGroup (Fin 5)) :
    (fixedPoints B (Fin 7)).ncard = 1 ∨ (fixedPoints B (Fin 7)).ncard = 2 := by
  classical
  let : IsSimpleGroup B := e.isSimpleGroup
  have hB : Nat.card B = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  obtain ⟨b, hb⟩ := exists_ne (1 : B)
  obtain ⟨i, hi⟩ : ∃ i : Fin 7, b.val.val i ≠ i := by
    by_contra! h
    apply hb
    apply Subtype.ext
    apply Subtype.ext
    exact Equiv.ext h
  have hnon : (orbit B i).ncard ≠ 1 := by
    intro h
    have hf := (mem_fixedPoints_iff_card_orbit_eq_one (M := B) (a := i)).mpr
      (by simpa only [Set.fintypeCard_eq_ncard] using h)
    exact hi (hf b)
  have ho := (orbit_card hB i).resolve_left hnon
  have hfix : fixedPoints B (Fin 7) = (orbit B i)ᶜ := by
    ext j
    constructor
    · intro hj hij
      have he : orbit B i = orbit B j := (orbit_eq_iff).mpr (mem_orbit_symm.mp hij)
      have hjc : (orbit B j).ncard = 1 := by
        simpa only [Set.fintypeCard_eq_ncard] using
          (mem_fixedPoints_iff_card_orbit_eq_one (M := B) (a := j)).mp hj
      exact hnon (he ▸ hjc)
    · intro hj
      have hdis : Disjoint (orbit B i) (orbit B j) := by
        apply Set.disjoint_left.mpr
        intro x hxi hxj
        have he := (orbit_eq_iff.mpr hxi).symm.trans (orbit_eq_iff.mpr hxj)
        exact hj (he ▸ mem_orbit_self j)
      have hsum : (orbit B i).ncard + (orbit B j).ncard ≤ 7 := by
        rw [← Set.ncard_union_eq hdis]
        simpa using Set.ncard_le_ncard (Set.subset_univ (orbit B i ∪ orbit B j))
      have hc := orbit_card hB j
      have hjc : (orbit B j).ncard = 1 := by omega
      apply (mem_fixedPoints_iff_card_orbit_eq_one (M := B) (a := j)).mpr
      simpa only [Set.fintypeCard_eq_ncard] using hjc
  have hs := Set.ncard_add_ncard_compl (orbit B i)
  rw [← hfix, Nat.card_fin] at hs
  omega

/-- A full Sylow two-normalizer rules out the transitive six-letter A₅ action. -/
theorem fixed_card_two (B : Subgroup A7) (e : B ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 A7) (hSN : (S : Subgroup A7) ≤ normalizer (B : Set A7)) :
    (fixedPoints B (Fin 7)).ncard = 2 := by
  classical
  rcases fixed_card B e with hfix | hfix
  · obtain ⟨i, hi⟩ := Set.ncard_eq_one.mp hfix
    have hif : i ∈ fixedPoints B (Fin 7) := by rw [hi]; simp
    have hNK : normalizer (B : Set A7) ≤ stabilizer A7 i := by
      intro g hg
      have hf : g • i ∈ fixedPoints B (Fin 7) := by
        intro b
        have hb := (mem_normalizer_iff''.mp hg b.val).mp b.property
        have hh := hif ⟨g⁻¹ * b.val * g, hb⟩
        change (g⁻¹ * b.val * g) • i = i at hh
        have hh' := congrArg (fun j : Fin 7 => g • j) hh
        change b.val • (g • i) = g • i
        simpa only [smul_smul, mul_inv_cancel_left, mul_assoc] using hh'
      exact Set.mem_singleton_iff.mp (hi ▸ hf)
    let K := stabilizer A7 i
    let N := (normalizer (B : Set A7)).subgroupOf K
    have hBK : B ≤ K := B.le_normalizer.trans hNK
    let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsSimpleGroup K := (AlternatingSix.SmallIndex.pointEquiv i).isSimpleGroup
    have hK : Nat.card K = 360 := by
      rw [Nat.card_congr (AlternatingSix.SmallIndex.pointEquiv i).toEquiv,
        nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    have hB : Nat.card B = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    have hS : Nat.card S = 8 := by
      let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [Sylow.card_eq_multiplicity, nat_card_alternatingGroup, Nat.card_fin]
      decide +kernel
    have hN : Nat.card N = Nat.card (normalizer (B : Set A7)) :=
      Nat.card_congr (subgroupOfEquivOfLe hNK).toEquiv
    have h60 : 60 ∣ Nat.card N := by
      rw [hN, ← hB]
      exact card_dvd_of_le B.le_normalizer
    have h8 : 8 ∣ Nat.card N := by
      rw [hN, ← hS]
      exact card_dvd_of_le hSN
    have h120 : 120 ∣ Nat.card N := by
      exact (show Nat.lcm 60 8 = 120 by decide) ▸ Nat.lcm_dvd h60 h8
    have hge := Nat.le_of_dvd (Nat.card_pos (α := N)) h120
    have hni := N.card_mul_index
    rw [hK] at hni
    have hiN : N.index ≤ 3 := by nlinarith
    have htop : N = ⊤ :=
      Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt N (by
        have hh := Nat.factorial_le hiN
        rw [hK]
        norm_num [Nat.factorial] at hh ⊢
        omega)
    have hKN : K ≤ normalizer (B : Set A7) := by
      intro g hg
      have hh : (⟨g, hg⟩ : K) ∈ N := by rw [htop]; trivial
      exact hh
    let : (B.subgroupOf K).Normal := normal_subgroupOf_iff_le_normalizer hBK |>.mpr hKN
    have hc : Nat.card (B.subgroupOf K) = 60 :=
      (Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv).trans hB
    rcases (inferInstance : (B.subgroupOf K).Normal).eq_bot_or_eq_top with h | h
    · rw [h, card_bot] at hc
      omega
    · rw [h, card_top, hK] at hc
      omega
  · exact hfix

/-- The actual A₅ is the pointwise stabilizer of its two fixed letters. -/
theorem exists_fixed_pair (B : Subgroup A7) (e : B ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 A7) (hSN : (S : Subgroup A7) ≤ normalizer (B : Set A7)) :
    ∃ i j : Fin 7, i ≠ j ∧ B = fixingSubgroup A7 ({i, j} : Set (Fin 7)) := by
  classical
  obtain ⟨i, j, hij, hfix⟩ := Set.ncard_eq_two.mp (fixed_card_two B e S hSN)
  refine ⟨i, j, hij, eq_of_le_of_card_ge ?_ ?_⟩
  · intro b hb k
    have hk : k.val ∈ fixedPoints B (Fin 7) := by rw [hfix]; exact k.property
    exact hk ⟨b, hb⟩
  · let F := fixingSubgroup A7 ({i, j} : Set (Fin 7))
    have he : F ≃* alternatingGroup (↑(({i, j} : Finset (Fin 7))ᶜ)) := by
      have hset : (({i, j} : Finset (Fin 7)) : Set (Fin 7)) = {i, j} := by
        ext x
        simp
      exact (MulEquiv.subgroupCongr (congrArg (fixingSubgroup A7) hset).symm).trans
        (Atlas.Families.Alternating.stabilizerComplementEquiv {i, j})
    have hc : Nat.card (↑(({i, j} : Finset (Fin 7))ᶜ)) = 5 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl]
      simp [hij]
    let : Nontrivial (↑(({i, j} : Finset (Fin 7))ᶜ)) :=
      Fintype.one_lt_card_iff_nontrivial.mp (by
        simpa only [← Nat.card_eq_fintype_card, hc] using (by decide : 1 < 5))
    have hf : Nat.card F = 60 := by
      rw [Nat.card_congr he.toEquiv, nat_card_alternatingGroup, hc]
      norm_num [Nat.factorial]
    change Nat.card F ≤ Nat.card B
    rw [hf, Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]

/-- A two-subgroup of the placed A₅ centralizes a genuine three-cycle. -/
theorem exists_centralizing_three (B : Subgroup A7) (e : B ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 A7) (hSN : (S : Subgroup A7) ≤ normalizer (B : Set A7))
    (P : Subgroup A7) (hP : IsPGroup 2 P) (hPB : P ≤ B) :
    ∃ c : A7, orderOf c = 3 ∧ ∀ a ∈ P, Commute a c := by
  classical
  have hBF : fixedPoints B (Fin 7) ⊆ fixedPoints P (Fin 7) := by
    intro i hi p
    exact hi ⟨p.val, hPB p.property⟩
  have hge : 2 ≤ (fixedPoints P (Fin 7)).ncard := by
    rw [← fixed_card_two B e S hSN]
    exact Set.ncard_le_ncard hBF
  have hm := hP.card_modEq_card_fixedPoints (Fin 7)
  rw [Nat.card_fin, Nat.card_coe_set_eq] at hm
  change 7 % 2 = (fixedPoints P (Fin 7)).ncard % 2 at hm
  obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ :=
    (Set.two_lt_ncard_iff).mp (show 2 < (fixedPoints P (Fin 7)).ncard by omega)
  let c : A7 := ⟨Equiv.swap i j * Equiv.swap i k, by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap hij,
      Equiv.Perm.sign_swap hik]
    decide⟩
  refine ⟨c, ?_, ?_⟩
  · rw [← Subgroup.orderOf_coe]
    exact (Equiv.Perm.isThreeCycle_swap_mul_swap_same hij hik hjk).orderOf
  · intro a ha
    apply Subtype.ext
    change a.val * (Equiv.swap i j * Equiv.swap i k) =
      (Equiv.swap i j * Equiv.swap i k) * a.val
    have hi' : a.val i = i := hi ⟨a, ha⟩
    have hj' : a.val j = j := hj ⟨a, ha⟩
    have hk' : a.val k = k := hk ⟨a, ha⟩
    rw [← mul_assoc, Equiv.mul_swap_eq_swap_mul a.val i j, hi', hj', mul_assoc,
      Equiv.mul_swap_eq_swap_mul a.val i k, hi', hk', ← mul_assoc]

end Theory.SpecificGroups.Alternating.SevenFivePlacement
