module
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.SylowFlags
public import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary
import Mathlib.LinearAlgebra.Transvection.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Order.Preorder.Finite

/-!
# Sylow overgroups in binary linear groups

Gaussian elimination and the adjacent-root relations identify every overgroup
of a Sylow two-subgroup with an actual partial-flag stabilizer. The proof extends
the five-dimensional calculation in `FiveFlagGeometry/SylowOvergroups` using
the dimension-independent elimination from `ThreeFreeSylowOvergroups`.
This supplies the flag assertions for both SL₄(2) and SL₅(2) in
Aschbacher--Smith 15.1.20(3e) and 15.1.22(7), printed pp.1094--1100.
-/

public section
open scoped MatrixGroups
namespace BinaryLinear.SylowFlagOvergroups
open OuterCyclic InvariantNodeActions Matrix.SpecialLinearGroup
variable {m : ℕ}
private noncomputable def standardBasis : Basis m := Pi.basisFun (ZMod 2) (Fin (m + 1))
private noncomputable def standardBorel : Subgroup (LinearGroup (m + 1)) :=
  cutStabilizer standardBasis Set.univ
private theorem mem_standard_cutSpace {m : ℕ} (i : Fin m) (v : Space (m + 1)) :
    v ∈ cutSpace standardBasis i ↔ ∀ j : Fin (m + 1), i.val < j.val → v j = 0 := by
  rw [cutSpace, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq]
  change (∀ j : Fin (m + 1), v j ≠ 0 → j.val ≤ i.val) ↔ _
  constructor
  · intro h j hj
    by_contra hv
    exact Nat.not_le_of_gt hj (h j hv)
  · intro h j hj
    by_contra hle
    exact hj (h j (Nat.lt_of_not_ge hle))

private theorem standard_fullFlag_iff_upperTriangular {m : ℕ}
    (A : SL(m + 1, ZMod 2)) :
    slEquivLinear (m + 1) A ∈ cutStabilizer standardBasis Set.univ ↔
      A.val.IsUpperTriangular := by
  rw [mem_cutStabilizer_maps]
  constructor
  · intro h i j hji
    let k : Fin m := ⟨j.val, by have := i.isLt; change j.val < i.val at hji; omega⟩
    have hv := h k (Set.mem_univ _) (standardBasis j)
      ((basis_mem_cutSpace _ k j).mpr le_rfl)
    have hz := (mem_standard_cutSpace k _).mp hv i hji
    simpa only [slEquivLinear_apply, standardBasis, Pi.basisFun_apply,
      Matrix.mulVec_single_one, Matrix.col_apply] using hz
  · intro h i _ v hv
    apply (mem_standard_cutSpace i _).mpr
    intro j hj
    rw [slEquivLinear_apply, Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : i.val < k.val
    · rw [(mem_standard_cutSpace i v).mp hv k hk, mul_zero]
    · rw [h (show k < j from by change k.val < j.val; omega), zero_mul]


private noncomputable def matrix (g : LinearGroup (m + 1)) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2) :=
  ((slEquivLinear (m + 1)).symm g).val

private theorem matrix_apply (g : LinearGroup (m + 1)) (i j : Fin (m + 1)) :
    matrix g i j = g (standardBasis j) i := by
  have h := congrFun (show (matrix g).mulVec (Pi.single j 1) = g (Pi.single j 1) from by
    rw [matrix, ← slEquivLinear_apply, MulEquiv.apply_symm_apply]) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, standardBasis, Pi.basisFun_apply] using h

private theorem mem_standardBorel_iff (g : LinearGroup (m + 1)) :
    g ∈ standardBorel ↔ (matrix g).IsUpperTriangular := by
  simpa only [MulEquiv.apply_symm_apply, standardBorel, matrix] using
    (standard_fullFlag_iff_upperTriangular ((slEquivLinear (m + 1)).symm g))

private noncomputable def permutation : Equiv.Perm (Fin (m + 1)) →* LinearGroup (m + 1) where
  toFun σ := standardBasis.equiv standardBasis σ
  map_one' := by
    apply standardBasis.ext'
    intro i
    simp
  map_mul' σ τ := by
    apply standardBasis.ext'
    intro i
    simp [LinearEquiv.mul_apply]

@[simp] private theorem permutation_basis (σ : Equiv.Perm (Fin (m + 1))) (i : Fin (m + 1)) :
    permutation σ (standardBasis i) = standardBasis (σ i) :=
  standardBasis.equiv_apply i standardBasis σ

private theorem basis_apply (i j : Fin (m + 1)) :
    standardBasis i j = if j = i then 1 else 0 := by
  simp [standardBasis, Pi.basisFun_apply, Pi.single_apply]

private theorem transvection_mem (f : Space (m + 1) →ₗ[ZMod 2] ZMod 2)
    (w : Space (m + 1)) (hw : f w = 0)
    (hupper : ∀ i j : Fin (m + 1), j < i → f (standardBasis j) * w i = 0) :
    LinearEquiv.transvection hw ∈ standardBorel := by
  apply (mem_standardBorel_iff _).mpr
  intro i j hji
  change j < i at hji
  rw [matrix_apply, LinearEquiv.transvection.apply]
  change standardBasis j i + f (standardBasis j) * w i = 0
  rw [basis_apply, if_neg (ne_of_gt hji), hupper i j hji, zero_add]

private theorem exists_pivot (v : Space (m + 1)) (hv : v ≠ 0) :
    ∃ p : Fin (m + 1), v p = 1 ∧ ∀ i : Fin (m + 1), p < i → v i = 0 := by
  classical
  have hn : (Finset.univ.filter fun i => v i ≠ 0).Nonempty := by
    by_contra h
    apply hv
    ext i
    have : ¬v i ≠ 0 := fun hi => h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    exact not_not.mp this
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun i => v i ≠ 0) (fun i => i) hn
  have hp0 := (Finset.mem_filter.mp hp).2
  refine ⟨p, (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hp0, ?_⟩
  intro i hi
  by_contra hzero
  exact (not_le_of_gt hi) (hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hzero⟩))

/-- The first `k` columns and their corresponding rows are isolated pivots. -/
private def Clean (g : LinearGroup (m + 1)) (k : ℕ) (s : Fin (m + 1) → Fin (m + 1)) : Prop :=
  ∀ j : Fin (m + 1), j.val < k →
    g (standardBasis j) = standardBasis (s j) ∧ ∀ x : Space (m + 1), g x (s j) = x j

private theorem clean_step (g : LinearGroup (m + 1)) (k : Fin (m + 1)) (s : Fin (m + 1) → Fin (m + 1))
    (hc : Clean g k.val s) :
    ∃ l ∈ standardBorel, ∃ r ∈ standardBorel, ∃ s' : Fin (m + 1) → Fin (m + 1),
      Clean (l * g * r) (k.val + 1) s' := by
  classical
  let v := g (standardBasis k)
  have hv : v ≠ 0 := by
    intro h
    have he : standardBasis k = 0 := g.injective (h.trans g.map_zero.symm)
    have := congrFun he k
    simp [basis_apply] at this
  obtain ⟨p, hp, hlast⟩ := exists_pivot v hv
  have hpk : ∀ j : Fin (m + 1), j.val < k.val → s j ≠ p := by
    intro j hj he
    have hz : v (s j) = 0 := by
      change g (standardBasis k) (s j) = 0
      rw [(hc j hj).2, basis_apply, if_neg (ne_of_lt (show j < k from hj))]
    rw [he, hp] at hz
    exact one_ne_zero hz
  -- Clear the pivot column by adding its pivot coordinate times `w`.
  let w : Space (m + 1) := v + standardBasis p
  have hw : (LinearMap.proj p : Space (m + 1) →ₗ[ZMod 2] ZMod 2) w = 0 := by
    change v p + standardBasis p p = 0
    simp [hp, basis_apply, CharTwo.add_self_eq_zero]
  let l : LinearGroup (m + 1) := LinearEquiv.transvection hw
  have hlx (x : Space (m + 1)) (i : Fin (m + 1)) : l x i = x i + x p * w i := rfl
  have hl : l ∈ standardBorel := by
    apply transvection_mem _ _ hw
    intro i j hji
    change standardBasis j p * w i = 0
    by_cases hjp : p = j
    · subst j
      have hpi : p ≠ i := ne_of_lt hji
      simp [w, hlast i hji, basis_apply, hpi.symm]
    · simp [basis_apply, hjp]
  have hlv : l v = standardBasis p := by
    ext i
    rw [hlx, hp, one_mul]
    change v i + (v i + standardBasis p i) = standardBasis p i
    exact CharTwo.add_cancel_left _ _
  have hwold (j : Fin (m + 1)) (hj : j.val < k.val) : w (s j) = 0 := by
    change g (standardBasis k) (s j) + standardBasis p (s j) = 0
    rw [(hc j hj).2]
    simp [basis_apply, ne_of_lt (show j < k from hj), hpk j hj]
  have hlold (j : Fin (m + 1)) (hj : j.val < k.val) :
      l (standardBasis (s j)) = standardBasis (s j) := by
    ext i
    rw [hlx]
    simp [basis_apply, (hpk j hj).symm]
  let h : LinearGroup (m + 1) := l * g
  have hhk : h (standardBasis k) = standardBasis p := hlv
  have hhcol (j : Fin (m + 1)) (hj : j.val < k.val) :
      h (standardBasis j) = standardBasis (s j) := by
    change l (g (standardBasis j)) = _
    rw [(hc j hj).1, hlold j hj]
  have hhrow (j : Fin (m + 1)) (hj : j.val < k.val) (x : Space (m + 1)) : h x (s j) = x j := by
    change l (g x) (s j) = x j
    rw [hlx, hwold j hj, mul_zero, add_zero, (hc j hj).2]
  -- Clear the pivot row by adding multiples of the newly isolated column.
  let f : Space (m + 1) →ₗ[ZMod 2] ZMod 2 :=
    (LinearMap.proj p).comp h.toLinearMap + LinearMap.proj k
  have hfx (x : Space (m + 1)) : f x = h x p + x k := rfl
  have hf : f (standardBasis k) = 0 := by
    rw [hfx, hhk]
    simp [basis_apply, CharTwo.add_self_eq_zero]
  have hfold (j : Fin (m + 1)) (hj : j.val < k.val) : f (standardBasis j) = 0 := by
    rw [hfx, hhcol j hj]
    simp [basis_apply, (hpk j hj).symm, ne_of_gt (show j < k from hj)]
  let r : LinearGroup (m + 1) := LinearEquiv.transvection hf
  have hrx (x : Space (m + 1)) : r x = x + f x • standardBasis k := rfl
  have hr : r ∈ standardBorel := by
    apply transvection_mem _ _ hf
    intro i j hji
    by_cases hik : i = k
    · subst i
      rw [hfold j hji, zero_mul]
    · simp [basis_apply, hik]
  let s' : Fin (m + 1) → Fin (m + 1) := fun j => if j = k then p else s j
  refine ⟨l, hl, r, hr, s', ?_⟩
  intro j hj
  change (h * r) (standardBasis j) = standardBasis (s' j) ∧
    ∀ x : Space (m + 1), (h * r) x (s' j) = x j
  by_cases hjk : j = k
  · subst j
    have hs : s' k = p := if_pos rfl
    rw [hs]
    constructor
    · change h (r (standardBasis k)) = _
      rw [hrx, hf, zero_smul, add_zero, hhk]
    · intro x
      change h (r x) p = x k
      rw [hrx, map_add, map_smul, hhk]
      change h x p + f x * standardBasis p p = x k
      rw [basis_apply, if_pos rfl, mul_one, hfx]
      exact CharTwo.add_cancel_left _ _
  · have hj' : j.val < k.val := by
      have hne : j.val ≠ k.val := fun e => hjk (Fin.ext e)
      omega
    have hs : s' j = s j := if_neg hjk
    rw [hs]
    constructor
    · change h (r (standardBasis j)) = _
      rw [hrx, hfold j hj', zero_smul, add_zero, hhcol j hj']
    · intro x
      change h (r x) (s j) = x j
      rw [hhrow j hj', hrx]
      change x j + f x * standardBasis k j = x j
      simp [basis_apply, hjk]

private theorem exists_clean (g : LinearGroup (m + 1)) :
    ∀ k : ℕ, k ≤ (m + 1) →
      ∃ a ∈ standardBorel, ∃ b ∈ standardBorel, ∃ s : Fin (m + 1) → Fin (m + 1),
        Clean (a * g * b) k s := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨1, standardBorel.one_mem, 1, standardBorel.one_mem, id, ?_⟩
    intro j hj
    omega
  | succ k ih =>
    intro hk
    obtain ⟨a, ha, b, hb, s, hs⟩ := ih (by omega)
    obtain ⟨l, hl, r, hr, s', hs'⟩ :=
      clean_step (a * g * b) ⟨k, by omega⟩ s hs
    refine ⟨l * a, standardBorel.mul_mem hl ha,
      b * r, standardBorel.mul_mem hb hr, s', ?_⟩
    simpa only [mul_assoc] using hs'

/-- Concrete upper-triangular/permutation/upper-triangular factorization. -/
private theorem hasBruhatDecomposition (g : LinearGroup (m + 1)) :
    ∃ u ∈ standardBorel, ∃ σ : Equiv.Perm (Fin (m + 1)),
      ∃ v ∈ standardBorel, g = u * permutation σ * v := by
  obtain ⟨a, ha, b, hb, s, hs⟩ := exists_clean g (m + 1) le_rfl
  have hcol (j : Fin (m + 1)) : (a * g * b) (standardBasis j) = standardBasis (s j) :=
    (hs j j.isLt).1
  have hinj : Function.Injective s := by
    intro i j hij
    apply standardBasis.injective
    apply (a * g * b).injective
    rw [hcol, hcol, hij]
  let σ : Equiv.Perm (Fin (m + 1)) :=
    Equiv.ofBijective s ⟨hinj, Finite.surjective_of_injective hinj⟩
  have heq : a * g * b = permutation σ := by
    apply standardBasis.ext'
    intro j
    rw [hcol, permutation_basis]
    rfl
  refine ⟨a⁻¹, standardBorel.inv_mem ha, σ, b⁻¹, standardBorel.inv_mem hb, ?_⟩
  rw [← heq]
  simp only [mul_assoc, mul_inv_cancel, mul_one, inv_mul_cancel_left]



private theorem matrix_mulVec (g : LinearGroup (m + 1)) (v : Space (m + 1)) :
    (matrix g).mulVec v = g v := by
  rw [matrix, ← slEquivLinear_apply, MulEquiv.apply_symm_apply]

private theorem cutStabilizer_antitone (b : Basis m) : Antitone (cutStabilizer b) := by
  intro s t hst g hg
  rw [mem_cutStabilizer] at hg ⊢
  exact fun i hi => hg i (hst hi)

private theorem mem_standard_cutStabilizer_iff (cuts : Set (Fin m)) (g : LinearGroup (m + 1)) :
    g ∈ cutStabilizer standardBasis cuts ↔
      ∀ k ∈ cuts, ∀ i j : Fin (m + 1), k.val < i.val → j.val ≤ k.val → matrix g i j = 0 := by
  rw [mem_cutStabilizer_maps]
  constructor
  · intro h k hk i j hi hj
    rw [matrix_apply]
    exact (mem_standard_cutSpace k _).mp
      (h k hk _ ((basis_mem_cutSpace standardBasis k j).mpr hj)) i hi
  · intro h k hk v hv
    apply (mem_standard_cutSpace k _).mpr
    intro i hi
    rw [← matrix_mulVec]
    change ∑ j, matrix g i j * v j = 0
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j.val ≤ k.val
    · rw [h k hk i j hi hj, zero_mul]
    · rw [(mem_standard_cutSpace k v).mp hv j (Nat.lt_of_not_ge hj), mul_zero]

private noncomputable def root (i j : Fin (m + 1)) : LinearGroup (m + 1) :=
  if h : i = j then 1 else slEquivLinear (m + 1) (Matrix.SpecialLinearGroup.transvection h (1 : ZMod 2))

private lemma root_apply {i j : Fin (m + 1)} (hij : i ≠ j) (v : Space (m + 1)) :
    root i j v = v + Pi.single i (v j) := by
  simp only [root, dif_neg hij, slEquivLinear_apply, transvection_coe,
    Matrix.add_mulVec, Matrix.single_mulVec_eq, Matrix.one_mulVec, one_mul]
  congr 1
  ext r
  by_cases h : r = i <;> simp [h]

private lemma root_basis {i j : Fin (m + 1)} (hij : i ≠ j) (k : Fin (m + 1)) :
    root i j (standardBasis k) =
      if k = j then standardBasis k + standardBasis i else standardBasis k := by
  rw [root_apply hij]
  by_cases h : k = j
  · subst k
    simp [standardBasis, Pi.basisFun_apply]
  · simp [h, standardBasis, Pi.basisFun_apply]

private lemma root_conj {i j : Fin (m + 1)} (hij : i ≠ j) (σ : Equiv.Perm (Fin (m + 1))) :
    permutation σ * root i j * (permutation σ)⁻¹ = root (σ i) (σ j) := by
  apply standardBasis.ext'
  intro k
  obtain ⟨k, rfl⟩ := σ.surjective k
  have hn : σ i ≠ σ j := σ.injective.ne hij
  simp only [LinearEquiv.mul_apply, ← map_inv, permutation_basis,
    Equiv.Perm.inv_def, Equiv.symm_apply_apply, root_basis hij, root_basis hn, σ.injective.eq_iff]
  split_ifs <;> simp only [map_add, permutation_basis]

private lemma root_chain {i j k : Fin (m + 1)} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    root i j * root j k = root j k * root i k * root i j := by
  simpa only [root, dif_neg hij, dif_neg hjk, dif_neg hik, ← map_mul, one_mul] using
    congrArg (slEquivLinear (m + 1))
      (Representation.OneCohomology.SLHigherNatural.transvection_chain hij hjk hik
        (1 : ZMod 2) 1)

private lemma matrix_root {i j : Fin (m + 1)} (hij : i ≠ j) :
    matrix (root i j) = 1 + Matrix.single i j 1 := by
  simp [root, hij, matrix, transvection_coe]

private lemma root_upper {i j : Fin (m + 1)} (hij : i < j) : root i j ∈ standardBorel := by
  rw [mem_standardBorel_iff, matrix_root hij.ne]
  intro r s hsr
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp_all
  omega

private lemma root_swap {i j : Fin (m + 1)} (hij : i ≠ j) :
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

private lemma root_chain_mem (P : Subgroup (LinearGroup (m + 1))) {i j k : Fin (m + 1)}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (h₁ : root i j ∈ P) (h₂ : root j k ∈ P) : root i k ∈ P := by
  have h : root j k * root i k * root i j ∈ P := by
    rw [← root_chain hij hjk hik]
    exact P.mul_mem h₁ h₂
  exact (P.mul_mem_cancel_left h₂).mp ((P.mul_mem_cancel_right h₁).mp h)

private lemma adjacent_mem_of_root (P : Subgroup (LinearGroup (m + 1))) (hBP : standardBorel ≤ P)
    {a b : Fin (m + 1)} (hab : root a b ∈ P) (k : Fin m)
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

private lemma exists_crossing_pair (σ : Equiv.Perm (Fin (m + 1))) (k : Fin m) (i : Fin (m + 1))
    (hi : i.val ≤ k.val) (hσi : k.val < (σ i).val) :
    ∃ j : Fin (m + 1), k.val < j.val ∧ (σ j).val ≤ k.val := by
  by_contra h
  push Not at h
  let f : {j : Fin (m + 1) // k.val < j.val} → {j : Fin (m + 1) // k.val < j.val} :=
    fun j => ⟨σ j, h j j.property⟩
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (σ.injective (congrArg Subtype.val hxy))
  obtain ⟨j, hj⟩ := (Finite.surjective_of_injective hf) ⟨σ i, hσi⟩
  have he : (j : Fin (m + 1)) = i := σ.injective (congrArg Subtype.val hj)
  have := j.property
  rw [he] at this
  omega

private lemma permutation_mem_flag_iff (cuts : Set (Fin m)) (σ : Equiv.Perm (Fin (m + 1))) :
    permutation σ ∈ cutStabilizer standardBasis cuts ↔
      ∀ k ∈ cuts, ∀ i : Fin (m + 1), i.val ≤ k.val → (σ i).val ≤ k.val := by
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

private lemma permutation_preserves_cuts (P : Subgroup (LinearGroup (m + 1))) (hBP : standardBorel ≤ P)
    (σ : Equiv.Perm (Fin (m + 1))) (hσ : permutation σ ∈ P) :
    permutation σ ∈ cutStabilizer standardBasis
      {k : Fin m | permutation (Equiv.swap k.castSucc k.succ) ∉ P} := by
  apply (permutation_mem_flag_iff _ σ).mpr
  intro k hk i hi
  by_contra hn
  obtain ⟨j, hj, hσj⟩ := exists_crossing_pair σ k i hi (Nat.lt_of_not_ge hn)
  have hij : i < j := by change i.val < j.val; omega
  have ht : root (σ i) (σ j) ∈ P := by
    rw [← root_conj hij.ne σ]
    exact P.mul_mem (P.mul_mem hσ (hBP (root_upper hij))) (P.inv_mem hσ)
  exact hk (adjacent_mem_of_root P hBP ht k hσj (Nat.lt_of_not_ge hn))

private lemma swap_mem_of_adjacent (P : Subgroup (LinearGroup (m + 1))) (i j : Fin (m + 1)) (hij : i < j)
    (h : ∀ k : Fin m, i.val ≤ k.val → k.val < j.val →
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

private lemma permutation_sides (cuts : Set (Fin m)) (σ : Equiv.Perm (Fin (m + 1)))
    (hσ : permutation σ ∈ cutStabilizer standardBasis cuts)
    (k : Fin m) (hk : k ∈ cuts) (i : Fin (m + 1)) :
    (σ i).val ≤ k.val ↔ i.val ≤ k.val := by
  constructor
  · intro hi
    have hInv : permutation σ⁻¹ ∈ cutStabilizer standardBasis cuts := by
      rw [map_inv]
      exact (cutStabilizer standardBasis cuts).inv_mem hσ
    have h := (permutation_mem_flag_iff cuts σ⁻¹).mp hInv k hk (σ i) hi
    simpa only [Equiv.Perm.inv_def, Equiv.symm_apply_apply] using h
  · exact (permutation_mem_flag_iff cuts σ).mp hσ k hk i

private lemma swap_mem_flag (cuts : Set (Fin m)) (i j : Fin (m + 1))
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

private lemma swap_mem_of_same_sides (P : Subgroup (LinearGroup (m + 1))) (cuts : Set (Fin m))
    (hadj : ∀ k : Fin m, k ∉ cuts → permutation (Equiv.swap k.castSucc k.succ) ∈ P)
    (i j : Fin (m + 1)) (hij : ∀ k ∈ cuts, i.val ≤ k.val ↔ j.val ≤ k.val) :
    permutation (Equiv.swap i j) ∈ P := by
  have hordered (i j : Fin (m + 1)) (hlt : i < j)
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

private lemma permutation_mem_of_flag (P : Subgroup (LinearGroup (m + 1))) (cuts : Set (Fin m))
    (hadj : ∀ k : Fin m, k ∉ cuts → permutation (Equiv.swap k.castSucc k.succ) ∈ P)
    (σ : Equiv.Perm (Fin (m + 1)))
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
private theorem standard_overgroups
    (P : Subgroup (LinearGroup (m + 1))) (hBP : standardBorel ≤ P) :
    ∃ cuts : Set (Fin m), P = cutStabilizer standardBasis cuts := by
  classical
  let cuts : Set (Fin m) := {k | permutation (Equiv.swap k.castSucc k.succ) ∉ P}
  have hBF : standardBorel ≤ cutStabilizer standardBasis cuts :=
    cutStabilizer_antitone standardBasis (Set.subset_univ cuts)
  have hadj (k : Fin m) (hk : k ∉ cuts) :
      permutation (Equiv.swap k.castSucc k.succ) ∈ P := not_not.mp hk
  refine ⟨cuts, ?_⟩
  apply Subgroup.ext
  intro g
  obtain ⟨u, hu, σ, v, hv, hg⟩ := hasBruhatDecomposition g
  have hP : g ∈ P ↔ permutation σ ∈ P := by
    rw [hg, P.mul_mem_cancel_right (hBP hv), P.mul_mem_cancel_left (hBP hu)]
  have hF : g ∈ cutStabilizer standardBasis cuts ↔
      permutation σ ∈ cutStabilizer standardBasis cuts := by
    rw [hg, (cutStabilizer standardBasis cuts).mul_mem_cancel_right (hBF hv),
      (cutStabilizer standardBasis cuts).mul_mem_cancel_left (hBF hu)]
  rw [hP, hF]
  exact ⟨permutation_preserves_cuts P hBP σ, permutation_mem_of_flag P cuts hadj σ⟩

/-- A Sylow overgroup is the stabilizer of a partial flag in a basis whose
complete flag is stabilized by that same Sylow subgroup. -/
theorem exists_flag_of_sylow_le
    (S : Sylow 2 (LinearGroup (m + 1))) (H : Subgroup (LinearGroup (m + 1)))
    (hSH : (S : Subgroup (LinearGroup (m + 1))) ≤ H) :
    ∃ (b : Basis m) (cuts : Set (Fin m)),
      (S : Subgroup (LinearGroup (m + 1))) = cutStabilizer b Set.univ ∧
      H = cutStabilizer b cuts := by
  obtain ⟨b, hb⟩ := sylow_eq_cutStabilizer S
  let g : LinearGroup (m + 1) := standardBasis.equiv b (Equiv.refl _)
  have hgb : standardBasis.map g = b := by
    ext i : 1
    change g (standardBasis i) = b i
    simp [g]
  have hB : standardBorel.map (MulAut.conj g).toMonoidHom =
      (S : Subgroup (LinearGroup (m + 1))) := by
    rw [standardBorel, cutStabilizer_map_conj, hgb, hb]
  let K := H.map (MulAut.conj g).symm.toMonoidHom
  have hBK : standardBorel ≤ K := by
    intro x hx
    apply Subgroup.mem_map_equiv.mpr
    apply hSH
    rw [← hB]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  obtain ⟨cuts, hK⟩ := standard_overgroups K hBK
  have he : K.map (MulAut.conj g).toMonoidHom = H :=
    (Subgroup.map_symm_eq_iff_map_eq K (e := MulAut.conj g) (H := H)).mp rfl
  refine ⟨b, cuts, hb, ?_⟩
  rw [← he, hK, cutStabilizer_map_conj, hgb]

end BinaryLinear.SylowFlagOvergroups
