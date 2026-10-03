module
public import Theory.GroupTheory.Commutator.SubnormalAbsorption
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.ElementaryAbelian.Basic
public import Theory.PGroupCore
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Subnormal actors with odd effective action

Let A be a normal elementary abelian two-subgroup of a finite group, and K
a subnormal subgroup. Suppose K/O2(K) has odd order, O2(K) centralizes A,
and K centralizes the center of O2(K). Then K centralizes A.

Schur-Zassenhaus supplies an odd complement to O2(K). Since O2(K) acts
trivially, coprime commutator idempotence gives M=[A,K]=[M,K]. Subnormal
commutator absorption puts M in K, and normality and its two-group order
put M in O2(K). The centralization assumptions then put M in its center
and kill [M,K], hence M.

This is the abstract transfer used twice in Stellmacher (6.4), journal
page 32. The source-facing caller supplies subnormality, the odd quotient,
and center centralization from the selected local groups. All commutators
are actual ambient subgroup commutators.
-/

open scoped commutatorElement IsMulCommutative
namespace Subgroup

private theorem commutator_le_iterated_of_coprime
    {G : Type*} [Group G] [Finite G] (A R : Subgroup G) [A.Normal]
    [IsMulCommutative A] (hcop : Nat.Coprime (Nat.card R) (Nat.card A)) :
    ⁅A, R⁆ ≤ ⁅⁅A, R⁆, R⁆ := by
  let _ : Normalizes R A := ⟨le_normalizer_of_normal⟩
  have hsolv : Group.IsSolvable A :=
    Group.isSolvable_of_comm fun a b => (IsMulCommutative.is_comm (M := A)).comm a b
  have heq := commutatorAction₂_eq_commutatorAction_of_solvable_coprime
    (G := A) (A := R) hsolv hcop
  have hmap := commutatorAction_subgroup_conj_map_eq_commutator A R le_normalizer_of_normal
  nth_rw 1 [← hmap, ← heq]
  rw [commutatorAction₂, commutatorSubgroup, MonoidHom.map_closure]
  apply (Subgroup.closure_le (K := ⁅⁅A, R⁆, R⁆)).mpr
  rintro x ⟨y, ⟨r, a, ha, rfl⟩, rfl⟩
  have haM : (a : G) ∈ ⁅A, R⁆ := by
    rw [← hmap]
    exact mem_map_of_mem A.subtype ha
  have hh := commutator_mem_commutator ((⁅A, R⁆).inv_mem haM) r.property
  simpa [commutatorElement_def,
    conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc] using hh

public theorem commutator_eq_bot_of_subnormal_odd_core_action
    {G : Type*} [Group G] [Finite G] (A K : Subgroup G)
    [A.Normal] [IsElementaryAbelian 2 A]
    (hK : K.IsSubnormal) (hodd : Odd (Nat.card (K ⧸ pCore 2 K)))
    (hcore : ⁅A, (pCore 2 K).map K.subtype⁆ = ⊥)
    (hcenter : ⁅(center ((pCore 2 K).map K.subtype)).map
      ((pCore 2 K).map K.subtype).subtype, K⁆ = ⊥) :
    ⁅A, K⁆ = ⊥ := by
  classical
  let Q := pCore 2 K
  let Qa := Q.map K.subtype
  have hQodd : Odd Q.index := by rw [index_eq_card]; exact hodd
  have hQcop : Nat.Coprime (Nat.card Q) Q.index := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
    rw [hn]
    exact hQodd.coprime_two_left.pow_left n
  obtain ⟨R0, hR0⟩ := exists_right_complement'_of_coprime hQcop
  let R := R0.map K.subtype
  have hRK : R ≤ K := map_subtype_le _
  have hRodd : Odd (Nat.card R) := by
    rw [card_map_of_injective K.subtype_injective, ← hR0.symm.index_eq_card]
    exact hQodd
  have hcop : Nat.Coprime (Nat.card R) (Nat.card A) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    rw [hn]
    exact hRodd.coprime_two_right.pow_right n
  have hAK : ⁅A, K⁆ = ⁅A, R⁆ := by
    apply le_antisymm
    · apply commutator_le.mpr
      intro a ha k hk
      have hkprod : (⟨k, hk⟩ : K) ∈ Q ⊔ R0 := by rw [hR0.sup_eq_top]; trivial
      obtain ⟨q, hq, r, hr, hqr⟩ := mem_sup_of_normal_left.mp hkprod
      have heq : k = (q : G) * r := (congrArg Subtype.val hqr).symm
      have haq : ⁅a, (q : G)⁆ = 1 := by
        have hh := commutator_mem_commutator ha (mem_map_of_mem K.subtype hq)
        rw [hcore] at hh
        exact hh
      rw [heq, commutatorElement_mul_right_eq_mul_conj, haq, one_mul]
      have har := commutator_mem_commutator ha (mem_map_of_mem K.subtype hr)
      have hqA : (q : G) ∈ centralizer (A : Set G) :=
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcore))
          (mem_map_of_mem K.subtype hq)
      have hc := mem_centralizer_iff.mp hqA ⁅a, (r : G)⁆
        ((commutator_le_left A R) har)
      simpa [← hc, mul_assoc] using har
    · exact commutator_mono le_rfl hRK
  let M := ⁅A, K⁆
  have hstable : M ≤ ⁅M, K⁆ := by
    change ⁅A, K⁆ ≤ ⁅⁅A, K⁆, K⁆
    rw [hAK]
    exact (commutator_le_iterated_of_coprime A R hcop).trans
      (commutator_mono le_rfl hRK)
  have hMK : M ≤ K := le_of_isSubnormal_of_le_commutator M K hK hstable
  have hMA : M ≤ A := commutator_le_left A K
  have hKM : K ≤ normalizer (M : Set G) := normalizer_commutator_ge_right A K
  let _ : (M.subgroupOf K).Normal :=
    (normal_subgroupOf_iff_le_normalizer hMK).mpr hKM
  have hMp : IsPGroup 2 M :=
    (IsElementaryAbelian.isPGroup 2 A).of_injective (inclusion hMA) (inclusion_injective hMA)
  have hMpK : IsPGroup 2 (M.subgroupOf K) :=
    hMp.of_equiv (subgroupOfEquivOfLe hMK).symm
  have hMQ : M ≤ Qa := by
    have hm : M.subgroupOf K ≤ Q := le_sSup ⟨inferInstance, hMpK⟩
    have hh := map_mono (f := K.subtype) hm
    rwa [map_subgroupOf_eq_of_le hMK] at hh
  have hMZ : M ≤ (center Qa).map Qa.subtype := by
    intro m hm
    refine ⟨⟨m, hMQ hm⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro q
    apply Subtype.ext
    exact mem_centralizer_iff.mp
      ((commutator_eq_bot_iff_le_centralizer.mp hcore) (hMA hm)) q q.property
  exact le_bot_iff.mp (hstable.trans ((commutator_mono hMZ le_rfl).trans_eq hcenter))

end Subgroup

