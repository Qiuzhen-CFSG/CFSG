module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary.Coordinates
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointQuotient
public import Mathlib.GroupTheory.Sylow

/-!
# The positive Sylow three-subgroup of PSU₄(3)

The literal upper unitriangular coordinate subgroup is a three-group: its
matrices have ninth power one. Any three-overgroup has a nonzero fixed vector
on the natural four-space. Two explicit unitary root elements force this
vector onto the first coordinate line. On its perpendicular quotient, a third
root element forces the middle block to be upper unitriangular. The unitary
last-row identity then puts the entire overgroup back in `positiveSU`.

Thus `positiveSU` is Sylow. Transport along the published, surjective
`coordinateProjection` retains the scalar quotient and proves that the literal
`positive` subgroup has index prime to three. No order formula or simplicity
assertion is used. `Index.Transfer` applies this to the covering-kernel bound.

Source: the defining-prime local calculation for Aschbacher--Smith I.1.4(5),
printed p.408 of `refs/quasithin.pdf`; GLS3 §6.1 and the unitary conventions in
chapter 2. The fixed-vector strategy follows `UnitaryFourSylow`, with its
characteristic-two root matrices replaced by verified characteristic-three
matrices.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourThree UnitaryFourThree.IsotropicStabilizers
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourPointQuotient

public noncomputable section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary
local notation "F" => FiniteField.Nine
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
local instance : CharP F 3 :=
  charP_of_card_eq_prime_pow (p := 3) (f := 2) (by decide)

private def ut {K : Type*} [Field K] (a b c d e f : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1,a,b,c; 0,1,d,e; 0,0,1,f; 0,0,0,1]

private theorem shape (g : CoordinateSU) (hg : g ∈ positiveGenerators) :
    g.val.val = ut (g.val.val 0 1) (g.val.val 0 2) (g.val.val 0 3)
      (g.val.val 1 2) (g.val.val 1 3) (g.val.val 2 3) := by
  obtain ⟨ht, hd⟩ := hg
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [ut, hd, ht]

private def upperMonoid : Submonoid CoordinateSU where
  carrier := positiveGenerators
  one_mem' := by
    constructor
    · intro i j h; simp [ne_of_gt h]
    · intro i; simp
  mul_mem' := by
    intro a b ha hb
    have hea := shape a ha
    have heb := shape b hb
    constructor
    · intro i j hij
      change (a.val.val * b.val.val) i j = 0
      rw [hea, heb]
      fin_cases i <;> fin_cases j <;>
        first | (solve | norm_num at hij) | simp [ut, Matrix.mul_apply, Fin.sum_univ_succ]
    · intro i
      change (a.val.val * b.val.val) i i = 1
      rw [hea, heb]
      fin_cases i <;> simp [ut, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem mem_positive (g : CoordinateSU) : g ∈ positiveSU ↔ g ∈ positiveGenerators := by
  constructor
  · intro h
    have hc : positiveSU.toSubmonoid ≤ upperMonoid := by
      rw [positiveSU, Subgroup.closure_toSubmonoid_of_finite]
      exact Submonoid.closure_le.mpr (fun _ h => h)
    exact hc h
  · exact fun h => Subgroup.subset_closure h

-- This local specialization follows `Mathlib.LinearAlgebra.Matrix.CharP`
-- (Aaron Anderson, 2020, Apache 2.0), using diagonal entries of scalar matrices.
private instance matrixCharThree {K : Type*} [Field K] [CharP K 3] :
    CharP (Matrix (Fin 4) (Fin 4) K) 3 where
  cast_eq_zero_iff k := by
    simp_rw [← diagonal_natCast, ← diagonal_zero, diagonal_eq_diagonal_iff,
      CharP.cast_eq_zero_iff K 3 k, forall_const]

private theorem ut_pow_nine {K : Type*} [Field K] [CharP K 3] (a b c d e f : K) : ut a b c d e f ^ 9 = 1 := by
  let N : Matrix (Fin 4) (Fin 4) K := !![0,a,b,c; 0,0,d,e; 0,0,0,f; 0,0,0,0]
  have hN2 : N ^ 2 = !![0,0,a*d,a*e+b*f; 0,0,0,d*f; 0,0,0,0; 0,0,0,0] := by
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;>
      simp [N, pow_two, Matrix.mul_apply, Fin.sum_univ_succ]
  have hN4 : N ^ 4 = 0 := by
    change N ^ (2 * 2) = 0
    rw [pow_mul, hN2]
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_succ]
  have hN9 : N ^ 9 = 0 := by
    rw [show 9 = 4 + 5 from rfl, pow_add, hN4, zero_mul]
  have hU : ut a b c d e f = 1 + N := by
    apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> simp [ut, N]
  rw [hU, show 9 = 3 ^ 2 from rfl, add_pow_char_pow_of_commute 3 2 (Commute.one_left N)]
  simp [hN9]

/-- The prescribed coordinate subgroup is a three-group. -/
theorem positiveSU_isThreeGroup : IsPGroup 3 positiveSU := by
  intro g
  refine ⟨2, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change g.val.val.val ^ 9 = 1
  rw [shape g.val ((mem_positive g.val).mp g.property)]
  exact ut_pow_nine _ _ _ _ _ _

local notation "ζ" => (⟨0,1⟩ : F)

private def rootMatrix (k : Fin 3) : Matrix (Fin 4) (Fin 4) F :=
  ![ut 0 (-1) 0 0 1 0, ut (-1) 0 0 0 0 1, ut 0 0 0 ζ 0 0] k

private theorem root_det (k : Fin 3) : (rootMatrix k).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · fin_cases k <;> simp [rootMatrix, ut, Fin.prod_univ_succ]
  · intro i j hij
    fin_cases k <;> fin_cases i <;> fin_cases j <;>
      first | (solve | norm_num at hij) | simp [rootMatrix, ut]

private theorem root_unitary (k : Fin 3) :
    coordinateForm.conjTranspose (rootMatrix k) * coordinateForm.form *
      rootMatrix k = coordinateForm.form := by
  fin_cases k <;> decide

private def root (k : Fin 3) : CoordinateSU :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (rootMatrix k)
    (by rw [root_det]; exact one_ne_zero), root_unitary k, Units.ext (root_det k)⟩

private theorem root_mem (k : Fin 3) : root k ∈ positiveSU := by
  apply Subgroup.subset_closure
  constructor
  · intro i j hij
    change rootMatrix k i j = 0
    fin_cases k <;> fin_cases i <;> fin_cases j <;>
      first | (solve | norm_num at hij) | simp [rootMatrix, ut]
  · intro i
    change rootMatrix k i i = 1
    fin_cases k <;> fin_cases i <;> simp [rootMatrix, ut]

private theorem overgroup_le_local (P : Subgroup CoordinateSU)
    (hP : IsPGroup 3 P) (hUP : positiveSU ≤ P) : P ≤ localSU F coordinateForm := by
  have hpV : 3 ∣ Nat.card (Fin 4 → F) := by
    simp
  have hz : (0 : Fin 4 → F) ∈ MulAction.fixedPoints P (Fin 4 → F) := by
    rw [MulAction.mem_fixedPoints]
    intro g
    exact smul_zero g
  obtain ⟨v, hv, hnv⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin 4 → F) hpV hz
  have hfix := MulAction.mem_fixedPoints.mp hv
  have hx := hfix ⟨root 0, hUP (root_mem 0)⟩
  have hy := hfix ⟨root 1, hUP (root_mem 1)⟩
  change rootMatrix 0 *ᵥ v = v at hx
  change rootMatrix 1 *ᵥ v = v at hy
  have hv1 : v 1 = 0 := by
    simpa [rootMatrix, ut, mulVec, dotProduct, Fin.sum_univ_succ] using congrFun hy 0
  have hv2 : v 2 = 0 := by
    simpa [rootMatrix, ut, mulVec, dotProduct, Fin.sum_univ_succ] using congrFun hx 0
  have hv3 : v 3 = 0 := by
    simpa [rootMatrix, ut, mulVec, dotProduct, Fin.sum_univ_succ] using congrFun hx 1
  have hv0 : v 0 ≠ 0 := by
    intro he
    apply hnv
    funext i
    fin_cases i <;> simp_all
  intro a ha
  have h := hfix ⟨a,ha⟩
  change a.val.val *ᵥ v = v at h
  have he (i : Fin 4) : a.val.val i 0 * v 0 = v i := by
    simpa [mulVec, dotProduct, Fin.sum_univ_succ, hv1,hv2,hv3] using congrFun h i
  apply (mem_localSU F _ a).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact mul_right_cancel₀ hv0 (by simpa using he 0)
  · exact (mul_eq_zero.mp ((he 1).trans hv1)).resolve_right hv0
  · exact (mul_eq_zero.mp ((he 2).trans hv2)).resolve_right hv0
  · exact (mul_eq_zero.mp ((he 3).trans hv3)).resolve_right hv0

private theorem overgroup_le_positive (P : Subgroup CoordinateSU)
    (hP : IsPGroup 3 P) (hUP : positiveSU ≤ P) : P ≤ positiveSU := by
  have hPL := overgroup_le_local P hP hUP
  let f : P →* GL (Fin 2) F :=
    (middleBlock F conjugation star_involutive).toHomUnits.comp
      (Subgroup.inclusion hPL)
  let : MulAction P (Fin 2 → F) := MulAction.compHom (Fin 2 → F) f
  have hpW : 3 ∣ Nat.card (Fin 2 → F) := by simp
  have hz : (0 : Fin 2 → F) ∈ MulAction.fixedPoints P (Fin 2 → F) := by
    rw [MulAction.mem_fixedPoints]
    intro g
    change (f g).val *ᵥ (0 : Fin 2 → F) = 0
    exact Matrix.mulVec_zero _
  obtain ⟨w, hw, hnw⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin 2 → F) hpW hz
  have hfix := MulAction.mem_fixedPoints.mp hw
  have hr := hfix ⟨root 2, hUP (root_mem 2)⟩
  change (!![1,ζ;0,1] : Matrix (Fin 2) (Fin 2) F) *ᵥ w = w at hr
  have hw1 : w 1 = 0 := by
    have he : ζ * w 1 = 0 := by
      simpa [mulVec, dotProduct, Fin.sum_univ_succ] using congrFun hr 0
    exact (mul_eq_zero.mp he).resolve_left (by decide)
  have hw0 : w 0 ≠ 0 := by
    intro hzero
    apply hnw
    funext i
    fin_cases i <;> simp_all
  intro g hg
  have hgfix := hfix ⟨g,hg⟩
  change (middleBlock F conjugation star_involutive ⟨g,hPL hg⟩) *ᵥ w = w at hgfix
  have h11 : g.val.val 1 1 = 1 := by
    apply mul_right_cancel₀ hw0
    simpa [middleBlock, mulVec, dotProduct, Fin.sum_univ_succ, hw1] using congrFun hgfix 0
  have h21 : g.val.val 2 1 = 0 := by
    have he : g.val.val 2 1 * w 0 = 0 := by
      simpa [middleBlock, mulVec, dotProduct, Fin.sum_univ_succ, hw1] using congrFun hgfix 1
    exact (mul_eq_zero.mp he).resolve_right hw0
  have h22 : g.val.val 2 2 = 1 := by
    have hd := middle_det F conjugation star_involutive ⟨g,hPL hg⟩
    simpa [middleBlock, Matrix.det_fin_two, h11,h21] using hd
  obtain ⟨h00,h10,h20,h30⟩ := (mem_localSU F coordinateForm g).mp (hPL hg)
  obtain ⟨_,h31,h32,h33⟩ := last_row F conjugation star_involutive g (hPL hg)
  apply Subgroup.subset_closure
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | (solve | norm_num at hij) | assumption
  · intro i
    fin_cases i <;> assumption

private def positiveSylowSU : Sylow 3 CoordinateSU :=
  { positiveSU with
    isPGroup' := positiveSU_isThreeGroup
    is_maximal' := by
      intro P hP hUP
      exact le_antisymm (overgroup_le_positive P hP hUP) hUP }

/-- The actual projective positive subgroup is a Sylow three-subgroup. -/
theorem positive_isSylow : ∃ P : Sylow 3 S, (P : Subgroup S) = positive :=
  ⟨positiveSylowSU.mapSurjective coordinateProjection_surjective, rfl⟩

/-- The index premise for the three-primary covering-kernel transfer. -/
theorem positive_not_three_dvd_index : ¬ 3 ∣ positive.index := by
  obtain ⟨P, hP⟩ := positive_isSylow
  rw [← hP]
  exact P.not_dvd_index
end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreePrimary
