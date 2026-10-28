module
public import Theory.SpecificGroups.SL2.BorelSupplementAction
public import Theory.GroupTheory.OddElementLift

/-!
# Odd-order representatives of binary linear Borel cosets

The matrix [[0,1],[1,1]] has order dividing three in characteristic two.
Conjugating it by an upper transvection places it in any specified nonbase
Borel coset. For an action whose stabilizer is the preimage of this literal
Borel, lift the matrix to an odd-order power of a preimage. This gives an
odd-order transporter between arbitrary points in the orbit, with no
hypothesis on the quotient kernel.

Source application: DGS, Groups and Graphs (1985), 6.5, printed p.122,
the odd-order neighbor transporter in the linear local action.
-/

open Subgroup Matrix
open scoped MatrixGroups
public section
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [CharP F 2]

private def cubic : SL(2,F) := ⟨!![0,1;1,1], by simp [det_fin_two,CharTwo.neg_eq]⟩

private theorem cubic_cube : (cubic : SL(2,F)) ^ 3 = 1 := by
  apply Subtype.ext
  change (!![0,1;1,1] : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ,Matrix.mul_apply,Fin.sum_univ_two,CharTwo.add_self_eq_zero]

/-- Every nonbase matrix Borel coset contains an odd-order element. -/
theorem exists_odd_borel_coset_mover (a : SL(2,F)) (ha : a ∉ rankOneBorel F) :
    ∃ x : SL(2,F), Odd (orderOf x) ∧ a⁻¹ * x ∈ rankOneBorel F := by
  have hc : a.val 1 0 ≠ 0 := fun hz => ha ((mem_rankOneBorel_iff a).mpr hz)
  let t := a.val 0 0 / a.val 1 0
  let u : SL(2,F) := transvection zero_ne_one t
  let x : SL(2,F) := u * cubic * u⁻¹
  have hx3 : x ^ 3 = 1 := by
    change (MulAut.conj u (cubic : SL(2,F))) ^ 3 = 1
    rw [←map_pow,cubic_cube,map_one]
  refine ⟨x,Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hx3),?_⟩
  rw [mem_rankOneBorel_iff]
  change (a⁻¹.val * (u.val * (cubic : SL(2,F)).val * u⁻¹.val)) 1 0 = 0
  simp [u,cubic,adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,t,CharTwo.neg_eq,
    transvection_coe,coe_inv]
  field_simp
  simp [CharTwo.add_self_eq_zero]

variable {J Ω : Type*} [Group J] [Finite J] [MulAction J Ω]
/-- The actual marked Borel stabilizer gives odd-order transport in the original action. -/
theorem exists_odd_mover_of_borel_stabilizer (q : J →* SL(2,F))
    (hq : Function.Surjective q) (o y : Ω)
    (hb : MulAction.stabilizer J o = (rankOneBorel F).comap q)
    (hy : ∃ b : J, b • o = y) :
    ∃ x : J, Odd (orderOf x) ∧ x • o = y := by
  by_cases he : y = o
  · exact ⟨1,by simp,by simpa only [one_smul] using he.symm⟩
  obtain ⟨b,rfl⟩ := hy
  have hbq : q b ∉ rankOneBorel F := by
    intro hc
    apply he
    change b ∈ MulAction.stabilizer J o
    rwa [hb]
  obtain ⟨a,ha,hba⟩ := exists_odd_borel_coset_mover (q b) hbq
  obtain ⟨g,hg⟩ := hq a
  obtain ⟨x,_,hx,hxq⟩ := q.exists_odd_power_with_image g (hg ▸ ha)
  have hfix : b⁻¹*x ∈ MulAction.stabilizer J o := by
    rw [hb]
    change q (b⁻¹*x) ∈ rankOneBorel F
    rw [map_mul,map_inv,hxq,hg]
    exact hba
  refine ⟨x,hx,?_⟩
  have hh := congrArg (fun z : Ω => b • z) hfix
  simpa only [mul_smul,smul_inv_smul] using hh
end Matrix.SpecialLinearGroup
