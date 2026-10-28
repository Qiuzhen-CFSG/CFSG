module

public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.ThreePrimary.MatrixTorus.Weyl
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.ThreeTorus.Matrix.Parameters
public import Theory.GroupTheory.NormalizedSupCard

/-!+# Full unitary torus and coordinate permutations for Ree descent

In the identity Hermitian form, the diagonal map (a,b) ↦
diag(a,(ab)⁻¹,b) is injective in SU₃. Its three-primary image has order
|C|², where C is the full Sylow three-subgroup of the norm-one units.
The coordinate cycle normalizes this image, meets it trivially, and triples
its order. The transposition exchanges its two generators in characteristic
two. All calculations precede projectivization, so the scalar three is retained.

The ambient matrix group used for descent includes the full norm-one torus
and both coordinate permutations. No Ree embedding is asserted here.

Source: GLS3 Example 2.6.3 and Table 4.7.3A, with the full SU₃ convention;
the matrix definitions are reused from the existing unitary torus development.
-/

@[expose] public noncomputable section

open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace ReeF4.CentralCovers.OddPrimary.Three.Unitary

open BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.ThreePrimary
open BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic

variable {F : Type*} [Field F] (J : HermitianForm 3 F) (hJ : J.form = 1)

def cycleSU : J.specialSubgroup := ⟨MatrixTorus.cycleGL, MatrixTorus.cycleGL_special J hJ⟩
def swapSU [CharP F 2] : J.specialSubgroup := ⟨MatrixTorus.swapGL, MatrixTorus.swapGL_special J hJ⟩

def monomial [CharP F 2] : Subgroup J.specialSubgroup :=
  (MatrixTorus.diagonalSpecial J hJ (HermitianForm.EvenInner.normOne J) (MatrixTorus.normOne_norm J)).range ⊔
    (zpowers (cycleSU J hJ) ⊔ zpowers (swapSU J hJ))

variable [CharP F 2]

def normDiagonal : (HermitianForm.EvenInner.normOne J × HermitianForm.EvenInner.normOne J) →*
    monomial J hJ :=
  (MatrixTorus.diagonalSpecial J hJ (HermitianForm.EvenInner.normOne J) (MatrixTorus.normOne_norm J)).codRestrict
    (monomial J hJ) (fun a => Subgroup.mem_sup_left (show _ ∈ MonoidHom.range _ from ⟨a, rfl⟩))

def cycle : monomial J hJ :=
  ⟨cycleSU J hJ, Subgroup.mem_sup_right (Subgroup.mem_sup_left (mem_zpowers _))⟩

def swap : monomial J hJ :=
  ⟨swapSU J hJ, Subgroup.mem_sup_right (Subgroup.mem_sup_right (mem_zpowers _))⟩

def primaryInclusion : OddThreeMatrix.primary J →* HermitianForm.EvenInner.normOne J :=
  Subgroup.inclusion (OddThreeMatrix.primary_le_normOne J)

def diagonal : (OddThreeMatrix.primary J × OddThreeMatrix.primary J) →* monomial J hJ :=
  (normDiagonal J hJ).comp ((primaryInclusion J).prodMap (primaryInclusion J))

def torus : Subgroup (monomial J hJ) := (diagonal J hJ).range

/-- A cyclic parameter generator gives the two marked torus generators. -/
theorem torus_generated (g : OddThreeMatrix.primary J)
    (hg : ∀ a : OddThreeMatrix.primary J, a ∈ zpowers g) :
    closure ({diagonal J hJ (g, 1), diagonal J hJ (1, g)} : Set _) = torus J hJ := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨(g, 1), rfl⟩
    · exact ⟨(1, g), rfl⟩
  · rintro x ⟨⟨a, b⟩, rfl⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp (hg a)
    obtain ⟨l, rfl⟩ := mem_zpowers_iff.mp (hg b)
    have he : (g ^ k, g ^ l) = (g, (1 : OddThreeMatrix.primary J)) ^ k * (1, g) ^ l := by
      simp
    rw [he, map_mul, map_zpow, map_zpow]
    exact mul_mem (zpow_mem (subset_closure (by simp)) k)
      (zpow_mem (subset_closure (by simp)) l)

theorem diagonal_injective : Function.Injective (diagonal J hJ) := by
  intro a b he
  have he' := congrArg (fun x : monomial J hJ => x.val.val.val) he
  apply Prod.ext
  · apply Subtype.ext
    apply Units.ext
    exact congrArg (fun A => A 0 0) he'
  · apply Subtype.ext
    apply Units.ext
    exact congrArg (fun A => A 2 2) he'

theorem cycle_diagonal (a : OddThreeMatrix.primary J × OddThreeMatrix.primary J) :
    cycle J hJ * diagonal J hJ a * (cycle J hJ)⁻¹ =
      diagonal J hJ ((a.1 * a.2)⁻¹, a.1) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycle, cycleSU, diagonal, normDiagonal, primaryInclusion,
      MatrixTorus.diagonalSpecial, MatrixTorus.diagonalGL_val, MatrixTorus.entries, MatrixTorus.cycleGL,
      Matrix.mul_apply, Fin.sum_univ_succ, mul_assoc, mul_comm]

theorem swap_diagonal (a : OddThreeMatrix.primary J × OddThreeMatrix.primary J) :
    swap J hJ * diagonal J hJ a * (swap J hJ)⁻¹ = diagonal J hJ (a.2, a.1) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swap, swapSU, diagonal, normDiagonal, primaryInclusion,
      MatrixTorus.diagonalSpecial, MatrixTorus.diagonalGL_val, MatrixTorus.entries, MatrixTorus.swapGL,
      Matrix.mul_apply, Fin.sum_univ_succ, mul_assoc, mul_comm]

theorem cycle_cube : cycle J hJ ^ 3 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycle, cycleSU, MatrixTorus.cycleGL, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem cycle_not_mem_torus : cycle J hJ ∉ torus J hJ := by
  rintro ⟨a, ha⟩
  have he := congrArg (fun x : monomial J hJ => x.val.val.val 0 1) ha
  simp [diagonal, normDiagonal, primaryInclusion, MatrixTorus.diagonalSpecial, MatrixTorus.diagonalGL_val,
    cycle, cycleSU, MatrixTorus.cycleGL] at he

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem cycle_order : orderOf (cycle J hJ) = 3 := by
  apply orderOf_eq_prime (cycle_cube J hJ)
  intro he
  exact cycle_not_mem_torus J hJ (he ▸ one_mem _)

theorem cycle_normalizes : cycle J hJ ∈ normalizer (torus J hJ : Set _) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨a, rfl⟩
    rw [cycle_diagonal]
    exact ⟨_, rfl⟩
  · rintro ⟨a, ha⟩
    have he : cycle J hJ * diagonal J hJ (a.2, (a.1 * a.2)⁻¹) * (cycle J hJ)⁻¹ =
        diagonal J hJ a := by
      rw [cycle_diagonal]
      congr 1
      ext <;> simp [mul_comm]
    have hx : x = diagonal J hJ (a.2, (a.1 * a.2)⁻¹) :=
      mul_left_cancel (mul_right_cancel (ha.symm.trans he.symm))
    exact ⟨_, hx.symm⟩

theorem cycle_disjoint_torus [Finite F] :
    Disjoint (torus J hJ) (zpowers (cycle J hJ)) := by
  classical
  rw [Subgroup.disjoint_def]
  intro x hx hy
  rw [mem_zpowers_iff_mem_range_orderOf, cycle_order] at hy
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
  have hn3 : n < 3 := Finset.mem_range.mp hn
  interval_cases n
  · simp
  · simp only [pow_one] at hx
    exact (cycle_not_mem_torus J hJ hx).elim
  · have h4 : (cycle J hJ ^ 2) ^ 2 = cycle J hJ := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, cycle_cube, pow_one, one_mul]
    exact (cycle_not_mem_torus J hJ (h4 ▸ pow_mem hx 2)).elim

theorem torus_card [Finite F] : Nat.card (torus J hJ) = Nat.card (OddThreeMatrix.primary J) ^ 2 := by
  rw [torus, ← Nat.card_congr (MonoidHom.ofInjective (diagonal_injective J hJ)).toEquiv,
    Nat.card_prod, pow_two]

theorem torus_join_card [Finite F] :
    Nat.card (torus J hJ ⊔ zpowers (cycle J hJ) : Subgroup (monomial J hJ)) =
      Nat.card (OddThreeMatrix.primary J) ^ 2 * 3 := by
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (zpowers_le.mpr (cycle_normalizes J hJ)) (cycle_disjoint_torus J hJ),
    torus_card, Nat.card_zpowers, cycle_order]

end ReeF4.CentralCovers.OddPrimary.Three.Unitary
