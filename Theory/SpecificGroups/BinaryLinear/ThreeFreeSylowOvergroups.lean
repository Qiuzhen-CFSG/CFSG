module
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.SylowFlags
import Mathlib.LinearAlgebra.Transvection.Basic
import Mathlib.Order.Preorder.Finite

/-!
# Three-free binary Sylow overgroups

An overgroup of a Sylow two-subgroup in a binary linear group whose order
is prime to three equals that Sylow subgroup. Gaussian elimination gives
an upper-triangular/permutation/upper-triangular factorization. A nonidentity
permutation has an inversion, so its overgroup contains two opposite root
transvections. Their product has order three. Sylow flag coordinates then
transport the standard-coordinate conclusion to the supplied Sylow.

The elimination argument generalizes the checked five-dimensional proof in
`FiveFlagGeometry/SylowOvergroups/Bruhat.lean`. The source application is the
finite-action calculation in Aschbacher--Smith, combined manuscript of
1 March 2004, 12.1.9, printed pp.793--794.
-/

public section

open scoped MatrixGroups
namespace BinaryLinear.ThreeFreeSylowOvergroups
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

private lemma matrix_root {i j : Fin (m + 1)} (hij : i ≠ j) :
    matrix (root i j) = 1 + Matrix.single i j 1 := by
  simp [root, hij, matrix, transvection_coe]

private lemma root_upper {i j : Fin (m + 1)} (hij : i < j) : root i j ∈ standardBorel := by
  rw [mem_standardBorel_iff, matrix_root hij.ne]
  intro r s hsr
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp_all
  omega


private theorem root_pair_cube {i j : Fin (m + 1)} (hij : i ≠ j) :
    (root i j * root j i) ^ 3 = 1 := by
  apply LinearEquiv.ext
  intro v
  ext k
  by_cases hki : k = i
  · subst k
    simp [pow_succ, LinearEquiv.mul_apply, root_apply hij, root_apply hij.symm,
      hij, hij.symm]
    ring_nf
    simp only [show (13 : ZMod 2) = 1 by decide, show (8 : ZMod 2) = 0 by decide,
      mul_one, mul_zero, add_zero]
  · by_cases hkj : k = j
    · subst k
      simp [pow_succ, LinearEquiv.mul_apply, root_apply hij, root_apply hij.symm,
        hij, hij.symm]
      ring_nf
      simp only [show (5 : ZMod 2) = 1 by decide, show (8 : ZMod 2) = 0 by decide,
        mul_one, mul_zero, add_zero]
    · simp [pow_succ, LinearEquiv.mul_apply, root_apply hij, root_apply hij.symm,
        Pi.single_apply, hki, hkj]

private theorem root_pair_ne_one {i j : Fin (m + 1)} (hij : i ≠ j) :
    root i j * root j i ≠ 1 := by
  intro he
  have h := congrArg (fun g : LinearGroup (m + 1) => g (standardBasis j)) he
  change root i j (root j i (standardBasis j)) = standardBasis j at h
  simp only [root_basis hij, root_basis hij.symm, if_neg hij.symm] at h
  have hz : standardBasis i = 0 := add_left_cancel (h.trans (add_zero _).symm)
  exact (standardBasis.ne_zero i) hz

/-- A binary complete-flag overgroup with order prime to three is the flag stabilizer. -/
private theorem eq_standardBorel_of_three_free (H : Subgroup (LinearGroup (m + 1)))
    (hBH : standardBorel ≤ H) (h3 : ¬3 ∣ Nat.card H) : H = standardBorel := by
  apply le_antisymm _ hBH
  intro g hg
  obtain ⟨u, hu, σ, v, hv, he⟩ := hasBruhatDecomposition g
  have hσ : permutation σ ∈ H := by
    have hh := H.mul_mem (H.mul_mem (H.inv_mem (hBH hu)) hg) (H.inv_mem (hBH hv))
    simpa only [he, mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using hh
  have hmono : StrictMono σ := by
    intro i j hij
    by_contra hle
    have hσne := σ.injective.ne hij.ne
    have hrev : σ j < σ i := lt_of_le_of_ne (le_of_not_gt hle) hσne.symm
    have hlow : root (σ i) (σ j) ∈ H := by
      rw [← root_conj hij.ne σ]
      exact H.mul_mem (H.mul_mem hσ (hBH (root_upper hij))) (H.inv_mem hσ)
    have hhigh := hBH (root_upper hrev)
    have hc : root (σ i) (σ j) * root (σ j) (σ i) ∈ H := H.mul_mem hlow hhigh
    have ho : orderOf (root (σ i) (σ j) * root (σ j) (σ i)) = 3 :=
      orderOf_eq_prime (root_pair_cube hσne) (root_pair_ne_one hσne)
    exact h3 (ho ▸ H.orderOf_dvd_natCard hc)
  have hσone : σ = 1 := by
    apply Equiv.ext
    intro i
    exact hmono.apply_eq
  rw [he, hσone, map_one, mul_one]
  exact standardBorel.mul_mem hu hv

/-- A three-free overgroup of an arbitrary binary Sylow two-subgroup equals it. -/
theorem eq_sylow_of_three_free (S : Sylow 2 (LinearGroup (m + 1)))
    (H : Subgroup (LinearGroup (m + 1))) (hSH : (S : Subgroup _) ≤ H)
    (h3 : ¬3 ∣ Nat.card H) : H = (S : Subgroup _) := by
  obtain ⟨b, hb⟩ := sylow_eq_cutStabilizer S
  let g : LinearGroup (m + 1) := standardBasis.equiv b (Equiv.refl _)
  let e := MulAut.conj g
  have hbasis : standardBasis.map g = b := by
    ext i
    simp [g]
  have hB : standardBorel.map e.toMonoidHom = (S : Subgroup _) := by
    rw [standardBorel, cutStabilizer_map_conj, hbasis, ← hb]
  let K := H.map e.symm.toMonoidHom
  have hBK : standardBorel ≤ K := by
    intro x hx
    have htx : e x ∈ (S : Subgroup _) := hB ▸ Subgroup.mem_map_of_mem e.toMonoidHom hx
    exact Subgroup.mem_map.mpr ⟨e x, hSH htx, e.symm_apply_apply x⟩
  have hcard : Nat.card K = Nat.card H :=
    (Nat.card_congr (H.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).toEquiv).symm
  have hK : K = standardBorel := eq_standardBorel_of_three_free K hBK (hcard ▸ h3)
  apply le_antisymm _ hSH
  intro x hx
  have hmem : e.symm x ∈ standardBorel := hK ▸ Subgroup.mem_map_of_mem e.symm.toMonoidHom hx
  rw [← hB]
  exact Subgroup.mem_map.mpr ⟨e.symm x, hmem, e.apply_symm_apply x⟩

end BinaryLinear.ThreeFreeSylowOvergroups
