module

public import Theory.SpecificGroups.Alternating.EightSylowResidual.Coordinates
public import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Bruhat factorization for the binary four-dimensional linear group

Every linear automorphism of the binary four-space is a product of two
standard complete-flag stabilizers with a coordinate permutation between them.

The proof isolates the columns successively. Choose the lowest nonzero entry
of the next column; it equals one over the binary field. An upper triangular
transvection clears the other entries of that column, and a second upper
triangular transvection clears the rest of its pivot row. The induction keeps
both the columns and rows already isolated. At the end invertibility makes
the four pivot positions a permutation, with column `i` sent to position `σ i`.

Adapted from `BinaryLinear.FiveFlagGeometry.SylowOvergroups.Bruhat`.
This supplies the concrete factorization for the intrinsic A₈ residual
comparison used in Aschbacher–Smith 3.3.21(e), printed p.596.
-/

public section

namespace BinaryLinear.FourSylowResidual
open OuterCyclic

private theorem basis_apply (i j : Fin 4) :
    standardBasis i j = if j = i then 1 else 0 := by
  simp [standardBasis, Pi.basisFun_apply, Pi.single_apply]

private theorem transvection_mem (f : Space 4 →ₗ[ZMod 2] ZMod 2)
    (w : Space 4) (hw : f w = 0)
    (hupper : ∀ i j : Fin 4, j < i → f (standardBasis j) * w i = 0) :
    LinearEquiv.transvection hw ∈ standardBorel := by
  apply (mem_standardBorel_iff _).mpr
  intro i j hji
  change j < i at hji
  rw [matrix_apply, LinearEquiv.transvection.apply]
  change standardBasis j i + f (standardBasis j) * w i = 0
  rw [basis_apply, if_neg (ne_of_gt hji), hupper i j hji, zero_add]

private theorem exists_pivot (v : Space 4) (hv : v ≠ 0) :
    ∃ p : Fin 4, v p = 1 ∧ ∀ i : Fin 4, p < i → v i = 0 := by
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
private def Clean (g : LinearGroup 4) (k : ℕ) (s : Fin 4 → Fin 4) : Prop :=
  ∀ j : Fin 4, j.val < k →
    g (standardBasis j) = standardBasis (s j) ∧ ∀ x : Space 4, g x (s j) = x j

private theorem clean_step (g : LinearGroup 4) (k : Fin 4) (s : Fin 4 → Fin 4)
    (hc : Clean g k.val s) :
    ∃ l ∈ standardBorel, ∃ r ∈ standardBorel, ∃ s' : Fin 4 → Fin 4,
      Clean (l * g * r) (k.val + 1) s' := by
  classical
  let v := g (standardBasis k)
  have hv : v ≠ 0 := by
    intro h
    have he : standardBasis k = 0 := g.injective (h.trans g.map_zero.symm)
    have := congrFun he k
    simp [basis_apply] at this
  obtain ⟨p, hp, hlast⟩ := exists_pivot v hv
  have hpk : ∀ j : Fin 4, j.val < k.val → s j ≠ p := by
    intro j hj he
    have hz : v (s j) = 0 := by
      change g (standardBasis k) (s j) = 0
      rw [(hc j hj).2, basis_apply, if_neg (ne_of_lt (show j < k from hj))]
    rw [he, hp] at hz
    exact one_ne_zero hz
  -- Clear the pivot column by adding its pivot coordinate times `w`.
  let w : Space 4 := v + standardBasis p
  have hw : (LinearMap.proj p : Space 4 →ₗ[ZMod 2] ZMod 2) w = 0 := by
    change v p + standardBasis p p = 0
    simp [hp, basis_apply, CharTwo.add_self_eq_zero]
  let l : LinearGroup 4 := LinearEquiv.transvection hw
  have hlx (x : Space 4) (i : Fin 4) : l x i = x i + x p * w i := rfl
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
  have hwold (j : Fin 4) (hj : j.val < k.val) : w (s j) = 0 := by
    change g (standardBasis k) (s j) + standardBasis p (s j) = 0
    rw [(hc j hj).2]
    simp [basis_apply, ne_of_lt (show j < k from hj), hpk j hj]
  have hlold (j : Fin 4) (hj : j.val < k.val) :
      l (standardBasis (s j)) = standardBasis (s j) := by
    ext i
    rw [hlx]
    simp [basis_apply, (hpk j hj).symm]
  let h : LinearGroup 4 := l * g
  have hhk : h (standardBasis k) = standardBasis p := hlv
  have hhcol (j : Fin 4) (hj : j.val < k.val) :
      h (standardBasis j) = standardBasis (s j) := by
    change l (g (standardBasis j)) = _
    rw [(hc j hj).1, hlold j hj]
  have hhrow (j : Fin 4) (hj : j.val < k.val) (x : Space 4) : h x (s j) = x j := by
    change l (g x) (s j) = x j
    rw [hlx, hwold j hj, mul_zero, add_zero, (hc j hj).2]
  -- Clear the pivot row by adding multiples of the newly isolated column.
  let f : Space 4 →ₗ[ZMod 2] ZMod 2 :=
    (LinearMap.proj p).comp h.toLinearMap + LinearMap.proj k
  have hfx (x : Space 4) : f x = h x p + x k := rfl
  have hf : f (standardBasis k) = 0 := by
    rw [hfx, hhk]
    simp [basis_apply, CharTwo.add_self_eq_zero]
  have hfold (j : Fin 4) (hj : j.val < k.val) : f (standardBasis j) = 0 := by
    rw [hfx, hhcol j hj]
    simp [basis_apply, (hpk j hj).symm, ne_of_gt (show j < k from hj)]
  let r : LinearGroup 4 := LinearEquiv.transvection hf
  have hrx (x : Space 4) : r x = x + f x • standardBasis k := rfl
  have hr : r ∈ standardBorel := by
    apply transvection_mem _ _ hf
    intro i j hji
    by_cases hik : i = k
    · subst i
      rw [hfold j hji, zero_mul]
    · simp [basis_apply, hik]
  let s' : Fin 4 → Fin 4 := fun j => if j = k then p else s j
  refine ⟨l, hl, r, hr, s', ?_⟩
  intro j hj
  change (h * r) (standardBasis j) = standardBasis (s' j) ∧
    ∀ x : Space 4, (h * r) x (s' j) = x j
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

private theorem exists_clean (g : LinearGroup 4) :
    ∀ k : ℕ, k ≤ 4 →
      ∃ a ∈ standardBorel, ∃ b ∈ standardBorel, ∃ s : Fin 4 → Fin 4,
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
theorem hasBruhatDecomposition : HasBruhatDecomposition := by
  intro g
  obtain ⟨a, ha, b, hb, s, hs⟩ := exists_clean g 4 le_rfl
  have hcol (j : Fin 4) : (a * g * b) (standardBasis j) = standardBasis (s j) :=
    (hs j j.isLt).1
  have hinj : Function.Injective s := by
    intro i j hij
    apply standardBasis.injective
    apply (a * g * b).injective
    rw [hcol, hcol, hij]
  let σ : Equiv.Perm (Fin 4) :=
    Equiv.ofBijective s ⟨hinj, Finite.surjective_of_injective hinj⟩
  have heq : a * g * b = permutation σ := by
    apply standardBasis.ext'
    intro j
    rw [hcol, permutation_basis]
    rfl
  refine ⟨a⁻¹, standardBorel.inv_mem ha, σ, b⁻¹, standardBorel.inv_mem hb, ?_⟩
  rw [← heq]
  simp only [mul_assoc, mul_inv_cancel, mul_one, inv_mul_cancel_left]

end BinaryLinear.FourSylowResidual
