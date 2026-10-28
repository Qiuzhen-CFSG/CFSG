module

public import Theory.SpecificGroups.Alternating.EightSylowResidual.Bruhat
public import Theory.GroupTheory.PResidual.TwoKernelComparison
public import Theory.GroupTheory.PResidual.NormalSubgroup
import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary
import Mathlib.GroupTheory.Perm.Sign

/-!
# Adjacent-swap generation of binary Sylow overgroups

Conjugating upper transvections by a permutation in an overgroup produces
lower roots. The three-index relation extracts every adjacent swap crossed
by such a root. Induction on permutation support then recovers the permutation
from available adjacent swaps. Bruhat factorization extends this to the whole
overgroup. Rank-one cubic elements will replace these swaps in the residual quotient.

Adapted from `BinaryLinear.FiveFlagGeometry.SylowOvergroups.StandardOvergroups`.
The consumer is the A₈ residual comparison in Aschbacher–Smith 3.3.21(e), p.596.
-/

namespace BinaryLinear.FourSylowResidual
open OuterCyclic Matrix.SpecialLinearGroup

private noncomputable def root (i j : Fin 4) : LinearGroup 4 :=
  if h : i = j then 1 else slEquivLinear 4 (Matrix.SpecialLinearGroup.transvection h (1 : ZMod 2))

private lemma root_apply {i j : Fin 4} (hij : i ≠ j) (v : Space 4) :
    root i j v = v + Pi.single i (v j) := by
  simp only [root, dif_neg hij, slEquivLinear_apply, transvection_coe,
    Matrix.add_mulVec, Matrix.single_mulVec_eq, Matrix.one_mulVec, one_mul]
  congr 1
  ext r
  by_cases h : r = i <;> simp [h]

private lemma root_basis {i j : Fin 4} (hij : i ≠ j) (k : Fin 4) :
    root i j (standardBasis k) =
      if k = j then standardBasis k + standardBasis i else standardBasis k := by
  rw [root_apply hij]
  by_cases h : k = j
  · subst k
    simp [standardBasis, Pi.basisFun_apply]
  · simp [h, standardBasis, Pi.basisFun_apply]

private lemma root_conj {i j : Fin 4} (hij : i ≠ j) (σ : Equiv.Perm (Fin 4)) :
    permutation σ * root i j * (permutation σ)⁻¹ = root (σ i) (σ j) := by
  apply standardBasis.ext'
  intro k
  obtain ⟨k, rfl⟩ := σ.surjective k
  have hn : σ i ≠ σ j := σ.injective.ne hij
  simp only [LinearEquiv.mul_apply, ← map_inv, permutation_basis,
    Equiv.Perm.inv_def, Equiv.symm_apply_apply, root_basis hij, root_basis hn, σ.injective.eq_iff]
  split_ifs <;> simp only [map_add, permutation_basis]

private lemma root_chain {i j k : Fin 4} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    root i j * root j k = root j k * root i k * root i j := by
  simpa only [root, dif_neg hij, dif_neg hjk, dif_neg hik, ← map_mul, one_mul] using
    congrArg (slEquivLinear 4)
      (Representation.OneCohomology.SLHigherNatural.transvection_chain hij hjk hik
        (1 : ZMod 2) 1)

private lemma matrix_root {i j : Fin 4} (hij : i ≠ j) :
    matrix (root i j) = 1 + Matrix.single i j 1 := by
  simp [root, hij, matrix, transvection_coe]

private lemma root_upper {i j : Fin 4} (hij : i < j) : root i j ∈ standardBorel := by
  rw [mem_standardBorel_iff, matrix_root hij.ne]
  intro r s hsr
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp_all
  omega

private lemma root_swap {i j : Fin 4} (hij : i ≠ j) :
    root i j * root j i * root i j = permutation (Equiv.swap i j) := by
  apply standardBasis.ext'
  intro k
  simp only [LinearEquiv.mul_apply, permutation_basis]
  by_cases hki : k = i
  · subst k
    simp [root_basis, hij, hij.symm, map_add]
    ext r
    simp only [Pi.add_apply]
    rw [add_comm (standardBasis j r), CharTwo.add_cancel_left]
  · by_cases hkj : k = j
    · subst k
      simp [root_basis, hij, hij.symm, map_add]
      ext r
      simp only [Pi.add_apply]
      rw [add_assoc, CharTwo.add_cancel_left, CharTwo.add_cancel_left]
    · simp [root_basis, hij, hij.symm, hki, hkj, Equiv.swap_apply_of_ne_of_ne]

private lemma root_chain_mem (P : Subgroup (LinearGroup 4)) {i j k : Fin 4}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (h₁ : root i j ∈ P) (h₂ : root j k ∈ P) : root i k ∈ P := by
  have h : root j k * root i k * root i j ∈ P := by
    rw [← root_chain hij hjk hik]
    exact P.mul_mem h₁ h₂
  exact (P.mul_mem_cancel_left h₂).mp ((P.mul_mem_cancel_right h₁).mp h)

private lemma adjacent_mem_of_root (P : Subgroup (LinearGroup 4)) (hBP : standardBorel ≤ P)
    {a b : Fin 4} (hab : root a b ∈ P) (k : Fin 3)
    (hb : b.val ≤ k.val) (ha : k.val < a.val) :
    permutation (Equiv.swap k.castSucc k.succ) ∈ P := by
  have hsb : k.succ ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hsc : k.succ ≠ k.castSucc := by simp [Fin.ext_iff]
  have h₁ : root k.succ b ∈ P := by
    by_cases h : k.succ = a
    · simpa only [h] using hab
    · have hsa : k.succ < a := by
        change k.val + 1 < a.val
        simp only [Fin.ext_iff, Fin.val_succ] at h
        omega
      exact root_chain_mem P hsa.ne (by intro he; subst a; omega) hsb
        (hBP (root_upper hsa)) hab
  have h₂ : root k.succ k.castSucc ∈ P := by
    by_cases h : b = k.castSucc
    · simpa only [h] using h₁
    · have hbc : b < k.castSucc := by
        change b.val < k.val
        simp only [Fin.ext_iff, Fin.val_castSucc] at h
        omega
      exact root_chain_mem P hsb hbc.ne hsc h₁ (hBP (root_upper hbc))
  rw [← root_swap hsc.symm]
  have hp : root k.castSucc k.succ ∈ P := hBP (root_upper (by simp))
  exact P.mul_mem (P.mul_mem hp h₂) hp

private lemma exists_crossing_pair (σ : Equiv.Perm (Fin 4)) (k : Fin 3) (i : Fin 4)
    (hi : i.val ≤ k.val) (hσi : k.val < (σ i).val) :
    ∃ j : Fin 4, k.val < j.val ∧ (σ j).val ≤ k.val := by
  by_contra h
  push Not at h
  let f : {j : Fin 4 // k.val < j.val} → {j : Fin 4 // k.val < j.val} :=
    fun j => ⟨σ j, h j j.property⟩
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (σ.injective (congrArg Subtype.val hxy))
  obtain ⟨j, hj⟩ := (Finite.surjective_of_injective hf) ⟨σ i, hσi⟩
  have he : (j : Fin 4) = i := σ.injective (congrArg Subtype.val hj)
  have := j.property
  rw [he] at this
  omega

private lemma permutation_mem_flag_iff (cuts : Set (Fin 3)) (σ : Equiv.Perm (Fin 4)) :
    permutation σ ∈ flagStabilizer standardBasis cuts ↔
      ∀ k ∈ cuts, ∀ i : Fin 4, i.val ≤ k.val → (σ i).val ≤ k.val := by
  rw [mem_standard_flagStabilizer_iff]
  constructor
  · intro h k hk j hj
    by_contra hn
    have he := h k hk (σ j) j (Nat.lt_of_not_ge hn) hj
    rw [matrix_apply, permutation_basis] at he
    simp [standardBasis] at he
  · intro h k hk i j hi hj
    have hn : i ≠ σ j := by
      intro he
      have := h k hk j hj
      rw [he] at hi
      omega
    rw [matrix_apply, permutation_basis]
    simp [standardBasis, hn]

private lemma permutation_preserves_cuts (P : Subgroup (LinearGroup 4)) (hBP : standardBorel ≤ P)
    (σ : Equiv.Perm (Fin 4)) (hσ : permutation σ ∈ P) :
    permutation σ ∈ flagStabilizer standardBasis
      {k : Fin 3 | permutation (Equiv.swap k.castSucc k.succ) ∉ P} := by
  apply (permutation_mem_flag_iff _ σ).mpr
  intro k hk i hi
  by_contra hn
  obtain ⟨j, hj, hσj⟩ := exists_crossing_pair σ k i hi (Nat.lt_of_not_ge hn)
  have hij : i < j := by change i.val < j.val; omega
  have ht : root (σ i) (σ j) ∈ P := by
    rw [← root_conj hij.ne σ]
    exact P.mul_mem (P.mul_mem hσ (hBP (root_upper hij))) (P.inv_mem hσ)
  exact hk (adjacent_mem_of_root P hBP ht k hσj (Nat.lt_of_not_ge hn))

private lemma swap_mem_of_adjacent (P : Subgroup (LinearGroup 4)) (i j : Fin 4) (hij : i < j)
    (h : ∀ k : Fin 3, i.val ≤ k.val → k.val < j.val →
      permutation (Equiv.swap k.castSucc k.succ) ∈ P) :
    permutation (Equiv.swap i j) ∈ P := by
  induction j using Fin.induction with
  | zero => exact (Fin.not_lt_zero i hij).elim
  | succ j ih =>
    have hj : permutation (Equiv.swap j.castSucc j.succ) ∈ P :=
      h j (Fin.le_castSucc_iff.mpr hij) (by simp)
    obtain he | hlt := (Fin.le_castSucc_iff.mpr hij).eq_or_lt
    · subst i
      exact hj
    · rw [Equiv.swap_comm, ← Equiv.swap_mul_swap_mul_swap (y := j.castSucc) hlt.ne hij.ne,
        map_mul, map_mul]
      exact P.mul_mem (P.mul_mem hj (ih hlt (fun k hik hkj => h k hik (by
        simp only [Fin.val_castSucc] at hkj
        simp only [Fin.val_succ]
        omega)))) hj

private lemma permutation_sides (cuts : Set (Fin 3)) (σ : Equiv.Perm (Fin 4))
    (hσ : permutation σ ∈ flagStabilizer standardBasis cuts)
    (k : Fin 3) (hk : k ∈ cuts) (i : Fin 4) :
    (σ i).val ≤ k.val ↔ i.val ≤ k.val := by
  constructor
  · intro hi
    have hInv : permutation σ⁻¹ ∈ flagStabilizer standardBasis cuts := by
      rw [map_inv]
      exact (flagStabilizer standardBasis cuts).inv_mem hσ
    have h := (permutation_mem_flag_iff cuts σ⁻¹).mp hInv k hk (σ i) hi
    simpa only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] using h
  · exact (permutation_mem_flag_iff cuts σ).mp hσ k hk i

private lemma swap_mem_flag (cuts : Set (Fin 3)) (i j : Fin 4)
    (hij : ∀ k ∈ cuts, i.val ≤ k.val ↔ j.val ≤ k.val) :
    permutation (Equiv.swap i j) ∈ flagStabilizer standardBasis cuts := by
  apply (permutation_mem_flag_iff cuts _).mpr
  intro k hk x hx
  by_cases hxi : x = i
  · subst x
    simpa using (hij k hk).mp hx
  · by_cases hxj : x = j
    · subst x
      simpa using (hij k hk).mpr hx
    · simpa only [Equiv.swap_apply_of_ne_of_ne hxi hxj] using hx

private lemma swap_mem_of_same_sides (P : Subgroup (LinearGroup 4)) (cuts : Set (Fin 3))
    (hadj : ∀ k : Fin 3, k ∉ cuts → permutation (Equiv.swap k.castSucc k.succ) ∈ P)
    (i j : Fin 4) (hij : ∀ k ∈ cuts, i.val ≤ k.val ↔ j.val ≤ k.val) :
    permutation (Equiv.swap i j) ∈ P := by
  have hordered (i j : Fin 4) (hlt : i < j)
      (hs : ∀ k ∈ cuts, i.val ≤ k.val ↔ j.val ≤ k.val) :
      permutation (Equiv.swap i j) ∈ P := by
    apply swap_mem_of_adjacent P i j hlt
    intro k hik hkj
    apply hadj k
    intro hk
    have := (hs k hk).mp hik
    omega
  rcases lt_trichotomy i j with hlt | he | hgt
  · exact hordered i j hlt hij
  · subst j
    rw [Equiv.swap_self]
    change permutation 1 ∈ P
    rw [map_one]
    exact P.one_mem
  · rw [Equiv.swap_comm]
    exact hordered j i hgt (fun k hk => (hij k hk).symm)

private lemma permutation_mem_of_flag (P : Subgroup (LinearGroup 4)) (cuts : Set (Fin 3))
    (hadj : ∀ k : Fin 3, k ∉ cuts → permutation (Equiv.swap k.castSucc k.succ) ∈ P)
    (σ : Equiv.Perm (Fin 4))
    (hσ : permutation σ ∈ flagStabilizer standardBasis cuts) : permutation σ ∈ P := by
  classical
  induction hn : σ.support.card using Nat.strong_induction_on generalizing σ with
  | h n ih =>
    by_cases he : σ = 1
    · subst σ
      simp
    · have hmove : ∃ i, σ i ≠ i := by
        by_contra h
        push Not at h
        exact he (Equiv.ext h)
      obtain ⟨i, hi⟩ := hmove
      have hsame : ∀ k ∈ cuts, i.val ≤ k.val ↔ (σ i).val ≤ k.val :=
        fun k hk => (permutation_sides cuts σ hσ k hk i).symm
      have hsP := swap_mem_of_same_sides P cuts hadj i (σ i) hsame
      have hsF := swap_mem_flag cuts i (σ i) hsame
      have hτ : permutation (Equiv.swap i (σ i) * σ) ∈ flagStabilizer standardBasis cuts := by
        rw [map_mul]
        exact (flagStabilizer standardBasis cuts).mul_mem hsF hσ
      have hsmaller : (Equiv.swap i (σ i) * σ).support.card < n := by
        rw [← hn]
        exact Equiv.Perm.card_support_swap_mul hi
      have hτP := ih _ hsmaller (Equiv.swap i (σ i) * σ) hτ rfl
      rw [map_mul] at hτP
      exact (P.mul_mem_cancel_left hsP).mp hτP

/-- An overgroup of the upper unitriangular group is generated by that group
and the adjacent permutation matrices it contains. -/
public theorem le_of_adjacent (P Q : Subgroup (LinearGroup 4))
    (hBP : standardBorel ≤ P) (hBQ : standardBorel ≤ Q)
    (hadj : ∀ k : Fin 3,
      permutation (Equiv.swap k.castSucc k.succ) ∈ P →
      permutation (Equiv.swap k.castSucc k.succ) ∈ Q) : P ≤ Q := by
  classical
  intro g hg
  obtain ⟨u, hu, σ, v, hv, rfl⟩ := hasBruhatDecomposition g
  have hσ : permutation σ ∈ P :=
    (P.mul_mem_cancel_left (hBP hu)).mp ((P.mul_mem_cancel_right (hBP hv)).mp hg)
  have hcuts := permutation_preserves_cuts P hBP σ hσ
  have hσQ := permutation_mem_of_flag Q
    {k : Fin 3 | permutation (Equiv.swap k.castSucc k.succ) ∉ P}
    (fun k hk => hadj k (not_not.mp hk)) σ hcuts
  exact Q.mul_mem (Q.mul_mem (hBQ hu) hσQ) (hBQ hv)

private lemma root_swap_cube {i j : Fin 4} (hij : i ≠ j) :
    (root i j * permutation (Equiv.swap i j)) ^ 3 = 1 := by
  apply standardBasis.ext'
  intro k
  change root i j (permutation (Equiv.swap i j)
    (root i j (permutation (Equiv.swap i j)
      (root i j (permutation (Equiv.swap i j) (standardBasis k)))))) = standardBasis k
  by_cases hki : k = i
  · subst k
    simp only [permutation_basis, Equiv.swap_apply_left, Equiv.swap_apply_right,
      root_basis hij, ite_true, if_neg hij, map_add]
    ext r
    simp only [Pi.add_apply]
    ring_nf
    simp only [show (2 : ZMod 2) = 0 by decide, show (3 : ZMod 2) = 1 by decide,
      mul_zero, mul_one, zero_add]
  · by_cases hkj : k = j
    · subst k
      simp only [permutation_basis, Equiv.swap_apply_left, Equiv.swap_apply_right,
        root_basis hij, ite_true, if_neg hij, map_add]
      ext r
      simp only [Pi.add_apply]
      ring_nf
      simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, zero_add]
    · simp only [permutation_basis, Equiv.swap_apply_of_ne_of_ne hki hkj,
        root_basis hij, if_neg hkj]

/-- The cubic residual and the actual Borel generate every Borel overgroup. -/
public theorem cubicResidual_sup_borel (P : Subgroup (LinearGroup 4))
    (hBP : standardBorel ≤ P) :
    Subgroup.primeToResidual 3 P ⊔ standardBorel.subgroupOf P = ⊤ := by
  let R := Subgroup.primeToResidual 3 P ⊔ standardBorel.subgroupOf P
  have hBQ : standardBorel ≤ R.map P.subtype := by
    intro b hb
    exact ⟨⟨b, hBP hb⟩, (show standardBorel.subgroupOf P ≤ R from le_sup_right) hb, rfl⟩
  have hPQ : P ≤ R.map P.subtype := by
    apply le_of_adjacent P _ hBP hBQ
    intro k hk
    have hr := root_upper (show k.castSucc < k.succ by simp)
    let r : P := ⟨root k.castSucc k.succ, hBP hr⟩
    let s : P := ⟨permutation (Equiv.swap k.castSucc k.succ), hk⟩
    have hc : (r * s) ^ (3 ^ 1) = 1 := by
      apply Subtype.ext
      exact root_swap_cube (by simp [Fin.ext_iff])
    have hrc : r * s ∈ R := (show Subgroup.primeToResidual 3 P ≤ R from le_sup_left)
      (Subgroup.mem_primeToResidual_of_pow hc)
    have hrr : r ∈ R := (show standardBorel.subgroupOf P ≤ R from le_sup_right) hr
    exact Subgroup.mem_map.mpr ⟨s, (R.mul_mem_cancel_left hrr).mp hrc, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := hPQ x.property
  have hyx : y = x := Subtype.ext he
  exact hyx ▸ hy

/-- In every actual Borel overgroup, O² and O^{3′} agree. -/
public theorem borel_overgroup_residuals (P : Subgroup (LinearGroup 4))
    (hBP : standardBorel ≤ P) :
    pResidual 2 P = Subgroup.primeToResidual 3 P := by
  let : Finite (LinearGroup 4) := Finite.of_injective
    (fun g : LinearGroup 4 => (g : Space 4 → Space 4)) DFunLike.coe_injective
  apply le_antisymm _ Subgroup.primeToResidual_three_le_twoResidual
  exact sInf_le ⟨inferInstance,
    Subgroup.isPGroup_quotient_of_sup_eq_top _ _ standardBorel_isPGroup.comap_subtype
      (cubicResidual_sup_borel P hBP)⟩

end BinaryLinear.FourSylowResidual
