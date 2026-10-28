module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortRoot
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Intrinsic description of the unitary short-root three-space

For fixed-field order q>2, the symmetric Hermitian three-space in the
plane residual is exactly [O₂(L), C_L(t)]. A fixed-field diagonal Levi
matrix expresses the marked long root as one of these commutators;
its normal closure supplies the reverse inclusion. The off-diagonal
trace shows that every action difference is symmetric. The short-root
line is exactly the central part of this three-space.

These descriptions let the full normalizer of L preserving t normalize
both subgroups without assuming an extension of its action to PSU₄.
Source: Aschbacher–Smith F.4.42, printed pp.295–296 of
`refs/quasithin.pdf`. The restriction q>2 retains the required q=4 row.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups
open Representation.OrthogonalFourMinus
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneLocal UnitaryFourPlaneRadical UnitaryFourShortRoot
open scoped commutatorElement
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortRoot
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "K" => FixedBy.subfield F σ
local notation "L" => localFactor F (form F σ hσ)
local notation "C" => shortCentralizer F σ hσ
local notation "Q" => Subgroup.subgroupOf (radical F σ hσ) (shortCentralizer F σ hσ)

omit [Finite F] [CharP F 2] in
/-- Fixed-field determinant-one congruence has symmetric action differences. -/
theorem congruence_difference_fixed (A : SpecialLinearGroup (Fin 2) F)
    (hA : A ∈ fixedSL F σ) (X : hermitianMatrices F σ) :
    hermitianCongruence F σ hσ A X - X ∈ fixedHermitian F σ := by
  have ha := (mem_fixedSL F σ A).mp hA
  have hx (i j : Fin 2) : σ (X.val i j) = X.val j i :=
    congrFun (congrFun X.property j) i
  have hd : A.val 0 0 * A.val 1 1 - A.val 0 1 * A.val 1 0 = 1 := by
    simpa only [det_fin_two] using A.property
  intro i j
  change σ ((hermitianCongruence F σ hσ A X).val i j - X.val i j) =
    (hermitianCongruence F σ hσ A X).val i j - X.val i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianCongruence, adjoint, Matrix.mul_apply, Fin.sum_univ_two, ha, hx]
  · ring
  · linear_combination (X.val 1 0 - X.val 0 1) * hd
  · linear_combination (X.val 0 1 - X.val 1 0) * hd
  · ring

/-- All commutators with the plane radical lie in the orthogonal three-space. -/
theorem centralizer_commutator_le_orthogonal :
    ⁅(⊤ : Subgroup C), Q⁆ ≤ (orthogonalRadical F σ hσ).subgroupOf C := by
  apply commutator_le.mpr
  intro a _ b hb
  obtain ⟨X,hX⟩ := (radicalEquiv F σ hσ).surjective ⟨b.val,hb⟩
  have hb' : radicalIntoCentralizer F σ hσ X = b :=
    Subtype.ext (congrArg (fun u : radical F σ hσ => u.val) hX)
  rw [←hb',commutatorElement_def,radicalIntoCentralizer_conj,←map_inv,←map_mul]
  refine ⟨Multiplicative.ofAdd
    (hermitianCongruence F σ hσ (factorRestriction F (form F σ hσ) a.val) X.toAdd - X.toAdd),
    congruence_difference_fixed F σ hσ _ ((mem_shortCentralizer F σ hσ _).mp a.property) _,?_⟩
  simp only [sub_eq_add_neg,ofAdd_add,ofAdd_neg,ofAdd_toAdd]
  rfl

/-- The marked long root generates the entire commutator space when q>2. -/
theorem centralizer_commutator_eq_orthogonal (hK : 2 < Nat.card K) :
    ⁅(⊤ : Subgroup C), Q⁆ = (orthogonalRadical F σ hσ).subgroupOf C := by
  apply le_antisymm (centralizer_commutator_le_orthogonal F σ hσ)
  rw [←long_normalClosure F σ hσ]
  apply normalClosure_le_normal
  rintro x rfl
  change longMark F σ hσ ∈ ⁅(⊤ : Subgroup C), Q⁆
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
  have hh := commutator_mem_commutator (H₁ := (⊤ : Subgroup C)) (H₂ := Q)
    (mem_top (fixedLevi F σ hσ ⟨A,hA⟩))
    (show radicalIntoCentralizer F σ hσ (Multiplicative.ofAdd X) ∈ Q from
      (radicalEquiv F σ hσ (Multiplicative.ofAdd X)).property)
  rw [commutatorElement_def,radicalIntoCentralizer_conj,←map_inv,←map_mul] at hh
  rw [←ofAdd_neg,←ofAdd_add,←sub_eq_add_neg] at hh
  simp only [fixedLevi,toAdd_ofAdd,factorRestriction_levi,he] at hh
  exact hh

/-- An intrinsic description inside the original determinant-one plane residual. -/
theorem orthogonal_eq_commutator (hK : 2 < Nat.card K) :
    orthogonalRadical F σ hσ = ⁅radical F σ hσ, C⁆ := by
  have he := congrArg (fun D : Subgroup C => D.map (C).subtype)
    (centralizer_commutator_eq_orthogonal F σ hσ hK)
  rw [map_commutator,←MonoidHom.range_eq_map,range_subtype,
    map_subgroupOf_eq_of_le (radical_le_shortCentralizer F σ hσ),
    map_subgroupOf_eq_of_le (orthogonalRadical_le_shortCentralizer F σ hσ),
    commutator_comm] at he
  exact he.symm

/-- The short-root line is the central part of the intrinsic three-space. -/
theorem shortLine_eq_orthogonal_inf_centralizer :
    shortLine F σ hσ = orthogonalRadical F σ hσ ⊓ centralizer (C : Set L) := by
  apply le_antisymm
  · intro x hx
    refine ⟨shortLine_le_orthogonal F σ hσ hx,?_⟩
    let y : C := ⟨x,orthogonalRadical_le_shortCentralizer F σ hσ
      (shortLine_le_orthogonal F σ hσ hx)⟩
    have hy : y ∈ center C := shortLine_le_center F σ hσ hx
    intro a ha
    exact congrArg (fun b : C => b.val) (mem_center_iff.mp hy ⟨a,ha⟩)
  · intro x hx
    exact (orthogonal_centralizer F σ hσ).le
      ⟨hx.1,(centralizer_le (fixedLeviGroup_le_centralizer F σ hσ)) hx.2⟩

end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourShortRoot
