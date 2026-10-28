module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# Elementary absorption by binary cubic block actors

A cubic actor on two coordinates expresses any shear from that block to
another as a commutator. The dual formula handles a shear into that block.
Since cubic elements lie in O² and O² is normal in the given subgroup,
these identities absorb every cross-block root having a partner in one
of its blocks. Explicit decreasing-row factorizations handle the complete
unitriangular kernels in degrees four and five, including central terms.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.25, printed p.960 (PDF p.977). These are identities in the actual
binary linear groups, with relative subgroup membership retained.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace BinaryLinear.CubicPairNormalizers.CoreAbsorption
open OuterCyclic

noncomputable def root {n : ℕ} (r s : Fin n) (hrs : r ≠ s) (a : ZMod 2) :
    LinearGroup n :=
  transvection (Pi.single r a) (LinearMap.proj s)
    (by simp [hrs.symm])

@[simp] theorem root_apply {n : ℕ} (r s : Fin n) (hrs : r ≠ s) (a : ZMod 2)
    (v : Space n) (k : Fin n) :
    root r s hrs a v k = v k + if k = r then v s * a else 0 := by
  simp [root, transvection, Pi.single_apply, eq_comm]

@[simp] theorem root_inv {n : ℕ} (r s : Fin n) (hrs : r ≠ s) (a : ZMod 2) :
    (root r s hrs a)⁻¹ = root r s hrs a := rfl

@[simp] theorem root_zero {n : ℕ} (r s : Fin n) (hrs : r ≠ s) :
    root r s hrs 0 = 1 := by ext v k; simp

noncomputable def cubic {n : ℕ} (r s : Fin n) (hrs : r ≠ s) : LinearGroup n :=
  root r s hrs 1 * root s r hrs.symm 1

theorem cubic_cube {n : ℕ} (r s : Fin n) (hrs : r ≠ s) :
    cubic r s hrs ^ 3 = 1 := by
  ext v k
  change cubic r s hrs (cubic r s hrs (cubic r s hrs v)) k = v k
  simp only [cubic, LinearEquiv.mul_apply, root_apply, mul_one]
  by_cases hkr : k = r <;> by_cases hks : k = s <;>
    simp [hkr, hks, hrs, hrs.symm] <;> ring_nf <;>
    simp only [show (13 : ZMod 2) = 1 by decide, show (8 : ZMod 2) = 0 by decide,
      show (5 : ZMod 2) = 1 by decide, mul_one, mul_zero, add_zero]

theorem root_row_commutator {n : ℕ} (r k s : Fin n)
    (hrk : r ≠ k) (hrs : r ≠ s) (hks : k ≠ s) :
    ⁅cubic r k hrk, root k s hks 1⁆ = root r s hrs 1 := by
  ext v t
  simp only [commutatorElement_def, cubic, mul_inv_rev, root_inv,
    LinearEquiv.mul_apply, root_apply, mul_one]
  by_cases htr : t = r <;> by_cases htk : t = k <;>
    simp [htr, htk, hrk, hrk.symm, hrs.symm, hks.symm] <;> ring_nf <;>
    simp only [show (2 : ZMod 2) = 0 by decide, show (3 : ZMod 2) = 1 by decide,
      show (4 : ZMod 2) = 0 by decide, show (5 : ZMod 2) = 1 by decide,
      mul_one, mul_zero, add_zero]

theorem root_column_commutator {n : ℕ} (r k s : Fin n)
    (hrk : r ≠ k) (hrs : r ≠ s) (hks : k ≠ s) :
    ⁅root r k hrk 1, cubic k s hks⁆ = root r s hrs 1 := by
  ext v t
  simp only [commutatorElement_def, cubic, mul_inv_rev, root_inv,
    LinearEquiv.mul_apply, root_apply, mul_one]
  by_cases htr : t = r <;> by_cases htk : t = k <;> by_cases hts : t = s <;>
    simp [htr, htk, hts, hrk, hrk.symm, hrs, hrs.symm, hks, hks.symm] <;> ring_nf <;>
    simp only [show (2 : ZMod 2) = 0 by decide, show (3 : ZMod 2) = 1 by decide,
      show (4 : ZMod 2) = 0 by decide, show (5 : ZMod 2) = 1 by decide,
      mul_one, mul_zero, add_zero]

/-- Every cross-block root is absorbed when one of its blocks has a second coordinate. -/
theorem root_mem_residual {n : ℕ} (c : Fin n → ℕ) (P : Subgroup (LinearGroup n))
    (hP : ∀ r s (hrs : r ≠ s), c r ≤ c s → root r s hrs 1 ∈ P)
    (r s : Fin n) (hrs : r ≠ s) (hcross : c r < c s)
    (hpartner : (∃ k, k ≠ r ∧ c k = c r) ∨ (∃ k, k ≠ s ∧ c k = c s)) :
    root r s hrs 1 ∈ (pResidual 2 P).map P.subtype := by
  have hc (i j : Fin n) (hij : i ≠ j) (hijc : c i = c j) :
      ∃ x : P, x.val = cubic i j hij ∧ x ∈ pResidual 2 P := by
    let x : P := ⟨cubic i j hij, P.mul_mem
      (hP i j hij hijc.le) (hP j i hij.symm hijc.symm.le)⟩
    refine ⟨x, rfl, mem_pResidual_of_orderOf_coprime ?_⟩
    have hx : x ^ 3 = 1 := Subtype.ext (cubic_cube i j hij)
    exact (by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hx)
  rcases hpartner with ⟨k, hkr, hk⟩ | ⟨k, hks, hk⟩
  · have hks : k ≠ s := by intro he; subst k; omega
    obtain ⟨x, hx, hxR⟩ := hc r k hkr.symm hk.symm
    let y : P := ⟨root k s hks 1, hP k s hks (by omega)⟩
    refine mem_map.mpr ⟨⁅x, y⁆, ?_, ?_⟩
    · exact commutator_le_left (pResidual 2 P) ⊤
        (commutator_mem_commutator hxR (mem_top y))
    · change ⁅x.val, y.val⁆ = _
      rw [hx]
      exact root_row_commutator r k s hkr.symm hrs hks
  · have hrk : r ≠ k := by intro he; subst k; omega
    obtain ⟨y, hy, hyR⟩ := hc k s hks hk
    let x : P := ⟨root r k hrk 1, hP r k hrk (by omega)⟩
    refine mem_map.mpr ⟨⁅x, y⁆, ?_, ?_⟩
    · exact commutator_le_right ⊤ (pResidual 2 P)
        (commutator_mem_commutator (mem_top x) hyR)
    · change ⁅x.val, y.val⁆ = _
      rw [hy]
      exact root_column_commutator r k s hrk hrs hks

/-- The actual coefficient matrix in the standard coordinates. -/
noncomputable def entries {n : ℕ} (g : LinearGroup n) :
    Matrix (Fin n) (Fin n) (ZMod 2) := fun r s => g (Pi.single s 1) r

/-- Decreasing row order makes the shear factorization free of cross terms. -/
theorem upper_five_mem (H : Subgroup (LinearGroup 5)) (g : LinearGroup 5)
    (hzero : ∀ r s : Fin 5, s < r → entries g r s = 0)
    (hdiag : ∀ r, entries g r r = 1)
    (hroot : ∀ r s (h : r < s), root r s (ne_of_lt h) (entries g r s) ∈ H) : g ∈ H := by
  let t (r s : Fin 5) (h : r < s) := root r s (ne_of_lt h) (entries g r s)
  have he : g = t 3 4 (by decide) * t 2 3 (by decide) * t 2 4 (by decide) *
      t 1 2 (by decide) * t 1 3 (by decide) * t 1 4 (by decide) *
      t 0 1 (by decide) * t 0 2 (by decide) * t 0 3 (by decide) * t 0 4 (by decide) := by
    apply LinearEquiv.toLinearMap_injective
    apply (Pi.basisFun (ZMod 2) (Fin 5)).ext
    intro j
    ext k
    simp only [Pi.basisFun_apply]
    change entries g k j = _
    fin_cases j <;> fin_cases k <;>
      simp [t, root_apply, hzero, hdiag]
  rw [he]
  repeat' apply H.mul_mem
  all_goals exact hroot _ _ (by decide)
/-- Decreasing row order makes the shear factorization free of cross terms. -/
theorem upper_four_mem (H : Subgroup (LinearGroup 4)) (g : LinearGroup 4)
    (hzero : ∀ r s : Fin 4, s < r → entries g r s = 0)
    (hdiag : ∀ r, entries g r r = 1)
    (hroot : ∀ r s (h : r < s), root r s (ne_of_lt h) (entries g r s) ∈ H) : g ∈ H := by
  let t (r s : Fin 4) (h : r < s) := root r s (ne_of_lt h) (entries g r s)
  have he : g = t 2 3 (by decide) * t 1 2 (by decide) * t 1 3 (by decide) *
      t 0 1 (by decide) * t 0 2 (by decide) * t 0 3 (by decide) := by
    apply LinearEquiv.toLinearMap_injective
    apply (Pi.basisFun (ZMod 2) (Fin 4)).ext
    intro j
    ext k
    simp only [Pi.basisFun_apply]
    change entries g k j = _
    fin_cases j <;> fin_cases k <;>
      simp [t, root_apply, hzero, hdiag]
  rw [he]
  repeat' apply H.mul_mem
  all_goals exact hroot _ _ (by decide)

end BinaryLinear.CubicPairNormalizers.CoreAbsorption

end
