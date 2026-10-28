module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionGraphPointCard
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot.Stabilizer

/-!
# The binary point centralizer of the marked short root

Commuting with I+E₀₂+E₁₃ forces a point-parabolic matrix to be triangular
and pairs its diagonal entries. Determinant one and the unitary equation
force the first diagonal entry into the binary fixed field and hence to one.
All diagonal entries are therefore one. This is the local matrix input for
C_M₁(t)=C_T(t) in Aschbacher–Smith F.5.5, printed p.301.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Matrix BenderSuzuki.MatrixGroups
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourShortRoot UnitaryFourSylow
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn

private theorem fixed_binary (x : F) (hx : σ x=x) : x=0 ∨ x=1 := by
  let a : PointLocal.FixedField 1 := ⟨x,hx⟩
  obtain ⟨b,hb,hu⟩ := (Nat.card_eq_two_iff' (0 : PointLocal.FixedField 1)).mp
    (PointLocal.fixedField_card 1 hn)
  have hb1 : (1 : PointLocal.FixedField 1)=b := hu 1 one_ne_zero
  by_cases ha : a=0
  · exact Or.inl (congrArg Subtype.val ha)
  · exact Or.inr (congrArg Subtype.val ((hu a ha).trans hb1.symm))

/-- A point-parabolic element commuting with the literal binary short root
is upper unitriangular. -/
theorem point_centralizer_short_le_upper
    (a : SU F (form F σ hσ)) (ha : a∈pointParabolicSU F (form F σ hσ))
    (hc : a * unipotentSU F σ hσ (shortParameter F σ) =
      unipotentSU F σ hσ (shortParameter F σ) * a) : a∈upper F σ hσ := by
  obtain ⟨h10,h20,h30⟩ := (mem_pointParabolicSU F _ a).mp ha
  have hp := centralizer_short_le_plane F σ hσ (mem_centralizer_singleton_iff.mpr hc)
  obtain ⟨_,_,h21,h31⟩ := (mem_planeParabolicSU F _ a).mp hp
  have hm := congrArg (fun b : SU F (form F σ hσ) => b.val.val) hc
  change a.val.val * unipotentMatrix F (shortParameter F σ).val =
    unipotentMatrix F (shortParameter F σ).val * a.val.val at hm
  have h02 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 0 2) hm
  have h13 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 1 3) hm
  have h12 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 1 2) hm
  simp [unipotentMatrix,shortParameter,mul_apply,Fin.sum_univ_succ,h10] at h02 h13 h12
  have hdiag02 : a.val.val 0 0=a.val.val 2 2 := add_right_cancel (h02.trans (add_comm _ _))
  have hdiag13 : a.val.val 1 1=a.val.val 3 3 := add_right_cancel (h13.trans (add_comm _ _))
  have hu := a.property.1
  change (form F σ hσ).conjTranspose a.val.val * gram F * a.val.val = gram F at hu
  have h03 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 0 3) hu
  simp [form,gram,HermitianForm.conjTranspose,mul_apply,Fin.sum_univ_succ,h10,h20,h30] at h03
  have ht : ∀ i j : Fin 4, j < i → a.val.val i j=0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hd := congrArg Units.val a.property.2
  change a.val.val.det=1 at hd
  rw [Matrix.det_of_isUpperTriangular ht] at hd
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one] at hd
  change a.val.val 0 0*(a.val.val 1 1*(a.val.val 2 2*a.val.val 3 3))=1 at hd
  have hd2 : (a.val.val 0 0 * a.val.val 1 1)^2=1 := by
    rw [←hdiag02,←hdiag13] at hd
    linear_combination hd
  have hd1 : a.val.val 0 0 * a.val.val 1 1=1 :=
    CharTwo.sq_injective (hd2.trans (one_pow 2).symm)
  have h00nz : a.val.val 0 0≠0 := by intro he;rw [he,zero_mul] at hd1;exact zero_ne_one hd1
  have h00fix : σ (a.val.val 0 0)=a.val.val 0 0 := by
    rw [←hdiag13] at h03
    exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one hd1) (h03.trans hd1.symm)
  have h00 : a.val.val 0 0=1 := (fixed_binary _ h00fix).resolve_left h00nz
  have h11 : a.val.val 1 1=1 := by simpa only [h00,one_mul] using hd1
  apply (mem_upper_iff_entries F σ hσ a).mpr
  refine ⟨ht,?_⟩
  intro j
  fin_cases j <;> simp_all

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
