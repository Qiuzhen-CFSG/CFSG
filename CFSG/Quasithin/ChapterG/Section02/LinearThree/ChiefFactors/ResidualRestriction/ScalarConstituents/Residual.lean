module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.Scalars
public import Theory.SpecificGroups.PSL3.LinearThreeLocalStructure
public import Mathlib.GroupTheory.PGroup
/-!
# The full point parabolic is two-perfect

The vector stabilizer is perfect for |F| ≥ 4. Together with the diagonal
scalar units it generates the full point parabolic. Over a field of order
2^n every scalar unit has odd order, so both pieces lie in O²(P).
The scalar character is retained for the constituent calculations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Hypothesis G.2.1 and G.2.5(8), printed pp.332,335–336.
This computes the prime residual, separately from the solvable residual.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents
open Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [Finite F]

def scalarValue : pointParabolicSL F →* F where
  toFun x := x.val.val 0 0
  map_one' := by simp
  map_mul' x y := by
    have hy := (mem_pointParabolicSL_iff F y).mp y.property
    simp [Matrix.mul_apply, Fin.sum_univ_three, hy.1, hy.2]

def scalar : pointParabolicSL F →* Fˣ := (scalarValue F).toHomUnits

@[simp] theorem scalar_coe (x : pointParabolicSL F) :
    (scalar F x : F) = x.val.val 0 0 := rfl

@[simp] theorem scalar_torus (a : Fˣ) : scalar F (pointTorusHom F a) = a := by
  apply Units.ext
  simp [scalar_coe, pointTorusHom, pointTorus]

private theorem perfect_residual (A : Type*) [Group A] [Finite A] [Group.IsPerfect A] :
    pResidual 2 A = ⊤ := by
  apply top_unique
  intro x _
  rw [pResidual, mem_sInf]
  rintro N ⟨hN, hp⟩
  let : N.Normal := hN
  have htop : N = ⊤ := by
    by_contra hne
    let : Nontrivial (A ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (A ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (A ⧸ N) := hp.isNilpotent
    exact Group.IsPerfect.not_isSolvable (A ⧸ N) inferInstance
  simp [htop]

omit [Finite F] in
theorem units_odd {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 0 < n) :
    Odd (Nat.card Fˣ) := by
  rw [Nat.card_units, hF]
  exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by decide))
    (Nat.even_pow.mpr ⟨by decide, by omega⟩) (by decide)

theorem twoResidual_eq_top (hcard : 4 ≤ Nat.card F) (hodd : Odd (Nat.card Fˣ)) :
    pResidual 2 (pointParabolicSL F) = ⊤ := by
  let R := (pResidual 2 (pointParabolicSL F)).map (pointParabolicSL F).subtype
  have hlocal : pointLocalSL F ≤ R := by
    let : Group.IsPerfect (pointLocalSL F) := pointLocalSL_isPerfect F hcard
    have h := map_pResidual_le 2 (inclusion (pointLocalSL_le F))
    rw [perfect_residual, ← MonoidHom.range_eq_map, inclusion_range] at h
    intro x hx
    exact ⟨⟨x, pointLocalSL_le F hx⟩, h hx, rfl⟩
  have htorus (a : Fˣ) : pointTorus F a ∈ R :=
    pointTorus_mem_twoResidual F a
      (hodd.coprime_two_left.of_dvd_right (_root_.orderOf_dvd_natCard a))
  apply top_unique
  intro x _
  let a := scalar F x
  have hx := (mem_pointParabolicSL_iff F x).mp x.property
  have hl : x.val * pointTorus F a⁻¹ ∈ pointLocalSL F := by
    rw [mem_pointLocalSL_iff]
    change (x.val.val * (pointTorus F a⁻¹).val) 0 0 = 1 ∧
      (x.val.val * (pointTorus F a⁻¹).val) 1 0 = 0 ∧
      (x.val.val * (pointTorus F a⁻¹).val) 2 0 = 0
    have ha : x.val.val 0 0 = (a : F) := rfl
    simp [pointTorus, Matrix.mul_diagonal, hx.1, hx.2, ha]
  have hm : x.val ∈ R := by
    have ht : pointTorus F a⁻¹ * pointTorus F a = 1 := by
      exact congrArg Subtype.val
        (show pointTorusHom F a⁻¹ * pointTorusHom F a = 1 by
          rw [← map_mul, inv_mul_cancel, map_one])
    have hh := R.mul_mem (hlocal hl) (htorus a)
    simpa only [mul_assoc, ht, mul_one] using hh
  obtain ⟨y, hy, he⟩ := hm
  exact (Subtype.ext he : y = x) ▸ hy

theorem larger_twoResidual_eq_top {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    pResidual 2 (pointParabolicSL F) = ⊤ := by
  apply twoResidual_eq_top F _ (units_odd F hF (by omega))
  rw [hF]
  exact (show 4 = 2 ^ 2 by decide) ▸ Nat.pow_le_pow_right (by decide) (by omega)
end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents
