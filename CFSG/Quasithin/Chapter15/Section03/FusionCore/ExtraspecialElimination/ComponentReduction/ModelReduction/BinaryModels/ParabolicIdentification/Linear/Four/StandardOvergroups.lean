module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four.Coordinates
import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary
import Mathlib.GroupTheory.Perm.Sign

/-!
# Standard Borel overgroups from Bruhat factorization

In the actual binary four-dimensional linear group, every overgroup of the
standard Borel stabilizes a standard partial flag. We assume only the concrete
Bruhat factorization supplied by `HasBruhatDecomposition`.

Choose the cuts whose adjacent permutation matrices are absent from the
overgroup. Conjugating upper transvections by a permutation, then applying the
three-index relation, shows that a permutation in the overgroup cannot cross
one of these cuts. Conversely, swaps within each consecutive block are products
of the available adjacent swaps. Induction on permutation support proves that
every permutation preserving the cuts belongs to the overgroup. Bruhat
factorization transfers these two implications to arbitrary linear maps.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), A.3.12,
printed pp.47--48, especially the characteristic-two parabolic argument on
p.48, and the L₄(2) branch of 15.3.49(l), printed p.1144. This is the conditional
standard-coordinate step; unconditional Sylow-overgroup exhaustion also needs
the separate proof of Bruhat factorization.
Adapted from this repository’s degree-five `FiveFlagGeometry.SylowOvergroups.StandardOvergroups`
proof, specialized to the degree-four branch of 15.3.49(l).
-/

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four
open Chapter2.ComponentRefinement.LieType.Binary Matrix.SpecialLinearGroup

private noncomputable def root (i j : Fin 4) : BinaryLinear.GL (Vector 4) :=
  if h : i = j then 1 else slEquivLinear 4 (Matrix.SpecialLinearGroup.transvection h (1 : ZMod 2))

private lemma root_apply {i j : Fin 4} (hij : i ≠ j) (v : Vector 4) :
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
  simp only [LinearEquiv.mul_apply, ← map_inv]
  have hbase : permutation σ⁻¹ (standardBasis (σ k)) = standardBasis k :=
    (permutation_basis σ⁻¹ (σ k)).trans (congrArg standardBasis (σ.symm_apply_apply k))
  rw [hbase, root_basis hij, root_basis hn]
  by_cases hk : k = j
  · subst k
    rw [if_pos rfl, if_pos rfl, map_add]
    exact congrArg₂ (· + ·) (permutation_basis σ j) (permutation_basis σ i)
  · rw [if_neg hk, if_neg (σ.injective.ne hk)]
    exact permutation_basis σ k

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
  simp only [LinearEquiv.mul_apply]
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

private lemma root_chain_mem (P : Subgroup (BinaryLinear.GL (Vector 4))) {i j k : Fin 4}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (h₁ : root i j ∈ P) (h₂ : root j k ∈ P) : root i k ∈ P := by
  have h : root j k * root i k * root i j ∈ P := by
    rw [← root_chain hij hjk hik]
    exact P.mul_mem h₁ h₂
  exact (P.mul_mem_cancel_left h₂).mp ((P.mul_mem_cancel_right h₁).mp h)

private lemma adjacent_mem_of_root (P : Subgroup (BinaryLinear.GL (Vector 4))) (hBP : standardBorel ≤ P)
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
    permutation σ ∈ cutStabilizer standardBasis cuts ↔
      ∀ k ∈ cuts, ∀ i : Fin 4, i.val ≤ k.val → (σ i).val ≤ k.val := by
  rw [mem_standard_cutStabilizer_iff]
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

private lemma permutation_preserves_cuts (P : Subgroup (BinaryLinear.GL (Vector 4))) (hBP : standardBorel ≤ P)
    (σ : Equiv.Perm (Fin 4)) (hσ : permutation σ ∈ P) :
    permutation σ ∈ cutStabilizer standardBasis
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

private lemma swap_mem_of_adjacent (P : Subgroup (BinaryLinear.GL (Vector 4))) (i j : Fin 4) (hij : i < j)
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
    (hσ : permutation σ ∈ cutStabilizer standardBasis cuts)
    (k : Fin 3) (hk : k ∈ cuts) (i : Fin 4) :
    (σ i).val ≤ k.val ↔ i.val ≤ k.val := by
  constructor
  · intro hi
    have hInv : permutation σ⁻¹ ∈ cutStabilizer standardBasis cuts := by
      rw [map_inv]
      exact (cutStabilizer standardBasis cuts).inv_mem hσ
    have h := (permutation_mem_flag_iff cuts σ⁻¹).mp hInv k hk (σ i) hi
    simpa only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] using h
  · exact (permutation_mem_flag_iff cuts σ).mp hσ k hk i

private lemma swap_mem_flag (cuts : Set (Fin 3)) (i j : Fin 4)
    (hij : ∀ k ∈ cuts, i.val ≤ k.val ↔ j.val ≤ k.val) :
    permutation (Equiv.swap i j) ∈ cutStabilizer standardBasis cuts := by
  apply (permutation_mem_flag_iff cuts _).mpr
  intro k hk x hx
  by_cases hxi : x = i
  · subst x
    simpa using (hij k hk).mp hx
  · by_cases hxj : x = j
    · subst x
      simpa using (hij k hk).mpr hx
    · simpa only [Equiv.swap_apply_of_ne_of_ne hxi hxj] using hx

private lemma swap_mem_of_same_sides (P : Subgroup (BinaryLinear.GL (Vector 4))) (cuts : Set (Fin 3))
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

private lemma permutation_mem_of_flag (P : Subgroup (BinaryLinear.GL (Vector 4))) (cuts : Set (Fin 3))
    (hadj : ∀ k : Fin 3, k ∉ cuts → permutation (Equiv.swap k.castSucc k.succ) ∈ P)
    (σ : Equiv.Perm (Fin 4))
    (hσ : permutation σ ∈ cutStabilizer standardBasis cuts) : permutation σ ∈ P := by
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
      have hτ : permutation (Equiv.swap i (σ i) * σ) ∈ cutStabilizer standardBasis cuts := by
        rw [map_mul]
        exact (cutStabilizer standardBasis cuts).mul_mem hsF hσ
      have hsmaller : (Equiv.swap i (σ i) * σ).support.card < n := by
        rw [← hn]
        exact Equiv.Perm.card_support_swap_mul hi
      have hτP := ih _ hsmaller (Equiv.swap i (σ i) * σ) hτ rfl
      rw [map_mul] at hτP
      exact (P.mul_mem_cancel_left hsP).mp hτP

/-- Every overgroup of the standard binary Borel is a standard partial-flag
stabilizer, assuming the explicit Bruhat factorization. The empty and full
sets of cuts allow the whole group and the Borel itself. -/
public theorem standard_overgroups_of_bruhat (hBruhat : HasBruhatDecomposition)
    (P : Subgroup (BinaryLinear.GL (Vector 4))) (hBP : standardBorel ≤ P) :
    ∃ cuts : Set (Fin 3), P = cutStabilizer standardBasis cuts := by
  classical
  let cuts : Set (Fin 3) := {k | permutation (Equiv.swap k.castSucc k.succ) ∉ P}
  have hBF : standardBorel ≤ cutStabilizer standardBasis cuts :=
    cutStabilizer_antitone standardBasis (Set.subset_univ cuts)
  have hadj (k : Fin 3) (hk : k ∉ cuts) :
      permutation (Equiv.swap k.castSucc k.succ) ∈ P := not_not.mp hk
  refine ⟨cuts, ?_⟩
  apply Subgroup.ext
  intro g
  obtain ⟨u, hu, σ, v, hv, hg⟩ := hBruhat g
  have hP : g ∈ P ↔ permutation σ ∈ P := by
    rw [hg, P.mul_mem_cancel_right (hBP hv), P.mul_mem_cancel_left (hBP hu)]
  have hF : g ∈ cutStabilizer standardBasis cuts ↔
      permutation σ ∈ cutStabilizer standardBasis cuts := by
    rw [hg, (cutStabilizer standardBasis cuts).mul_mem_cancel_right (hBF hv),
      (cutStabilizer standardBasis cuts).mul_mem_cancel_left (hBF hu)]
  rw [hP, hF]
  exact ⟨permutation_preserves_cuts P hBP σ, permutation_mem_of_flag P cuts hadj σ⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four
