module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeFour.Smallness

/-!
# A common cubic and its two marked endpoint involutions

Choose a generator of the units of the native four-field. Its diagonal
matrix gives a cubic in the whole Borel. The two standard Weyl involutions
invert its projective image; for the second endpoint this calculation uses
the scalar quotient, rather than asserting an equality in SL₃.

Both involutions and the cubic are then transported through the original
completion maps. The two compatibility squares identify the same cubic in
both endpoints, and injectivity keeps both involutions outside the whole
Borel. No relation between their images in the ambient completion is assumed.

Source: Aschbacher–Smith 5.2.16, printed p.655 (`refs/quasithin.pdf`).
The ambient cubic normalizer constructs the final short product in
`LinearCompletion.lean`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.M23Completion
open CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour
open CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeFour.Native
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
local notation "F" => Matrix.PSL3Four.F
local notation "PSL" => Matrix.PSL3Four.PSL

private theorem first_square (i : Bool) : (first i)^2=1 := by
  have hh : (firstSL i)^2=1 := by
    rw [pow_two]
    apply Subtype.ext
    change (firstSL i).val * (firstSL i).val = 1
    cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;>
      simp [firstSL,Matrix.mul_apply,Fin.sum_univ_three]
  simpa only [first,map_pow,map_one] using congrArg (projection F) hh

private theorem first_order (i : Bool) : orderOf (first i)=2 :=
  orderOf_eq_prime (first_square i) (fun hh => first_not_mem i (hh ▸ one_mem _))

private theorem first_out_borel (i : Bool) : first i ∉ borel F := by
  intro hh
  apply first_not_mem i
  cases i
  · simpa only [Bool.not_false,Completion.family_true,model_right_range] using
      CFSG.Quasithin.ChapterF.GreenBook.LieModels.LinearThree.borel_le_line F hh
  · simpa only [Bool.not_true,Completion.family_false,model_left_range] using
      CFSG.Quasithin.ChapterF.GreenBook.LieModels.LinearThree.borel_le_point F hh

private theorem cubic_seed :
    ∃ b : borel F, orderOf b = 3 ∧
      ∀ i : Bool, first i*(b:PSL)*(first i)⁻¹=(b:PSL)⁻¹ := by
  classical
  have hcard : Nat.card Fˣ = 3 := by
    let := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card,Fintype.card_units,←Nat.card_eq_fintype_card,Matrix.PSL3Four.card_F]
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rw [hcard])
  have ha3 : a^3=1 := by simpa only [ha] using pow_orderOf_eq_one a
  have hane : a ≠ 1 := by intro hh; simp only [hh,orderOf_one] at ha; omega
  let b : borel F := ⟨torusMap F (1,a),torus_le_borel F ⟨(1,a),rfl⟩⟩
  have hpow : b^3=1 := by
    apply Subtype.ext
    change torusMap F (1,a)^3=1
    rw [←map_pow]
    have hh : (1,a)^3=(1 : Fˣ × Fˣ) := Prod.ext (one_pow 3) ha3
    rw [hh,map_one]
  have hbne : b ≠ 1 := by
    intro hh
    have hk : torusSL F (1,a) ∈ (projection F).ker := congrArg Subtype.val hh
    rw [projection_ker,Matrix.SpecialLinearGroup.mem_center_iff] at hk
    obtain ⟨r,_,hr⟩ := hk
    have h0 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 0) hr
    have h2 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 2 2) hr
    have hr1 : r=1 := by simpa [torusSL_val,Matrix.scalar_apply] using h0
    have hra : r=(a:F) := by simpa [torusSL_val,Matrix.scalar_apply] using h2
    exact hane (Units.ext (hra.symm.trans hr1))
  refine ⟨b,orderOf_eq_prime hpow hbne,?_⟩
  intro i
  have hiinv : (first i)⁻¹=first i := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using first_square i)
  rw [hiinv]
  apply mul_eq_one_iff_eq_inv.mp
  change projection F (firstSL i) * projection F (torusSL F (1,a)) *
      projection F (firstSL i) * projection F (torusSL F (1,a)) = 1
  rw [←map_mul,←map_mul,←map_mul,←MonoidHom.mem_ker,projection_ker,
    Matrix.SpecialLinearGroup.mem_center_iff]
  have hav : (a:F)^3=1 := congrArg Units.val ha3
  have hainv : (a:F)^2=(a⁻¹:Fˣ) :=
    congrArg Units.val (mul_eq_one_iff_eq_inv.mp ((pow_succ a 2).symm.trans ha3))
  cases i
  · refine ⟨1,by simp,?_⟩
    change Matrix.scalar (Fin 3) (1:F) = (firstSL false).val *
      (torusSL F (1,a)).val * (firstSL false).val * (torusSL F (1,a)).val
    ext j k; fin_cases j <;> fin_cases k <;>
      simp [torusSL_val,firstSL,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three,
        Matrix.scalar_apply,Units.val_inv_eq_inv_val,a.ne_zero]
  · refine ⟨(a⁻¹:Fˣ),?_,?_⟩
    · simpa only [Fintype.card_fin,Units.val_inv_eq_inv_val,inv_pow,inv_one] using congrArg Inv.inv hav
    · change Matrix.scalar (Fin 3) (↑(a⁻¹):F) = (firstSL true).val *
        (torusSL F (1,a)).val * (firstSL true).val * (torusSL F (1,a)).val
      ext j k; fin_cases j <;> fin_cases k <;>
        simp [torusSL_val,firstSL,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three,
          Matrix.scalar_apply,Units.val_inv_eq_inv_val,←pow_two,hainv]

/-- A common cubic and its two inverting endpoint involutions are constructed
through the actual whole-overlap maps of the completion. -/
theorem completion_seeds {X : Type*} [Group X] (c : Completion X) :
    ∃ b s t : X, b ∈ c.middle.range ∧ orderOf b=3 ∧
      s ∈ c.left.range ∧ t ∈ c.right.range ∧
      s ∉ c.middle.range ∧ t ∉ c.middle.range ∧
      orderOf s=2 ∧ orderOf t=2 ∧ s*b*s⁻¹=b⁻¹ ∧ t*b*t⁻¹=b⁻¹ := by
  obtain ⟨b,hb,hbi⟩ := cubic_seed
  let s₀ : pointParabolic F := ⟨first false,by simpa only [Completion.family_false,model_left_range] using first_mem false⟩
  let t₀ : lineParabolic F := ⟨first true,by simpa only [Completion.family_true,model_right_range] using first_mem true⟩
  let s := c.left s₀
  let t := c.right t₀
  have hbR : c.middle b = c.right
      ((CFSG.Quasithin.ChapterF.GreenBook.LieModels.LinearThree.amalgam F).right b) :=
    DFunLike.congr_fun c.compatible b
  refine ⟨c.middle b,s,t,⟨b,rfl⟩,(orderOf_injective c.middle c.middle_injective b).trans hb,
    ⟨s₀,rfl⟩,⟨t₀,rfl⟩,?_,?_,?_,?_,?_,?_⟩
  · rintro ⟨a,ha⟩
    have hh := congrArg Subtype.val (c.left_injective ha)
    change (a:PSL)=first false at hh
    exact first_out_borel false (hh ▸ a.property)
  · rintro ⟨a,ha⟩
    rw [DFunLike.congr_fun c.compatible a] at ha
    have hh := congrArg Subtype.val (c.right_injective ha)
    change (a:PSL)=first true at hh
    exact first_out_borel true (hh ▸ a.property)
  · exact (orderOf_injective c.left c.left_injective s₀).trans
      ((Subgroup.orderOf_coe s₀).symm.trans (first_order false))
  · exact (orderOf_injective c.right c.right_injective t₀).trans
      ((Subgroup.orderOf_coe t₀).symm.trans (first_order true))
  · exact (by
      change c.left s₀*c.left _*(c.left s₀)⁻¹=(c.left _)⁻¹
      rw [←map_inv,←map_inv,←map_mul,←map_mul]
      apply congrArg c.left
      exact Subtype.ext (hbi false))
  · rw [hbR]
    change c.right t₀*c.right _*(c.right t₀)⁻¹=(c.right _)⁻¹
    rw [←map_inv,←map_inv,←map_mul,←map_mul]
    apply congrArg c.right
    exact Subtype.ext (hbi true)
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.M23Completion
