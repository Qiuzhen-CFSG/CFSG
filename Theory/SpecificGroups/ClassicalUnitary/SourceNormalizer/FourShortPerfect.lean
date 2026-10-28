module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortAction
public import Theory.GroupTheory.SolvableResidual

/-!
# A perfect subgroup containing the unitary short-root line

For fixed-field order greater than three, the fixed Levi SL₂ is perfect,
so lies in the solvable residual of the actual short-root centralizer.
A diagonal Levi commutator with the Hermitian radical is the marked long
root. Normality therefore puts that root, and its whole normal closure,
in the perfect residual. In particular the full q-element short-root
line can be carried into the same perfect actor in the maximal-W argument.

Source: Aschbacher–Smith F.4.42, printed p.296; the diagonal calculation
also underlies `FourShortNormalizer.centralizer_commutator_eq_orthogonal`.
-/

public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
open Representation.OrthogonalFourMinus
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneLocal UnitaryFourPlaneRadical UnitaryFourShortRoot
open scoped commutatorElement
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortRoot
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "K" => FixedBy.subfield F σ
local notation "C" => shortCentralizer F σ hσ

/-- The actual long-root marker lies in the perfect residual of its short-root centralizer. -/
theorem longMark_mem_solvableResidual (hK : 3 < Nat.card K) :
    longMark F σ hσ ∈ solvableResidual C := by
  let : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three _ hK
  let : Group.IsPerfect (fixedLeviHom F σ hσ).range :=
    Group.IsPerfect.range _
  obtain ⟨r,hr0,hr1⟩ := ENat.exists_ne_ne_of_three_le
    (α := K) (by rw [ENat.card_eq_coe_natCard]; exact_mod_cast (by omega : 3 ≤ Nat.card K)) 0 1
  have hrF : (r:F) ≠ 0 := fun he => hr0 (Subtype.ext he)
  have hr2 : r^2 - 1 ≠ 0 := by
    intro he
    rcases sq_eq_one_iff.mp (sub_eq_zero.mp he) with he | he
    · exact hr1 he
    · exact hr1 (by simpa only [CharTwo.neg_eq] using he)
  have hrfix : σ (r:F) = r := r.property
  let b : K := (r^2 - 1)⁻¹
  let A : SpecialLinearGroup (Fin 2) F :=
    ⟨!![(r:F),0;0,(r:F)⁻¹],by simp [det_fin_two,hrF]⟩
  have hA : A ∈ fixedSL F σ := by
    rw [mem_fixedSL]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [A,hrfix]
  let X := symmetric F σ b 0 0
  have he : hermitianCongruence F σ hσ A X - X = longParameter F σ := by
    have hb : ((r:F)^2 - 1) * (b:F) = 1 := by
      exact congrArg Subtype.val (mul_inv_cancel₀ hr2)
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hermitianCongruence,A,X,symmetric,fixedHermitianEquiv,
        longParameter,adjoint,Matrix.vecMul,dotProduct,Fin.sum_univ_two,hrfix]
    linear_combination hb
  have hlevi : fixedLevi F σ hσ ⟨A,hA⟩ ∈ solvableResidual C := by
    obtain ⟨B,hB⟩ := hA
    apply le_solvableResidual_of_isPerfect (fixedLeviHom F σ hσ).range
    refine ⟨B,?_⟩
    apply Subtype.ext
    change levi F σ hσ (SpecialLinearGroup.map (FixedBy.subfield F σ).subtype B) = _
    rw [hB]
    rfl
  have hh' := (commutator_le_left (solvableResidual C) (⊤ : Subgroup C))
    (commutator_mem_commutator hlevi
      (mem_top (radicalIntoCentralizer F σ hσ (Multiplicative.ofAdd X))))
  rw [commutatorElement_def,radicalIntoCentralizer_conj,←map_inv,←map_mul] at hh'
  rw [←ofAdd_neg,←ofAdd_add,←sub_eq_add_neg] at hh'
  simp only [fixedLevi,toAdd_ofAdd,factorRestriction_levi,he] at hh'
  exact hh'

end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortRoot
