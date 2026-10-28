module

public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.ProjectiveGraphField.Monomial
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.ProjectiveFixer.Candidate
public import Theory.GroupTheory.QuaternionGenerated
public import Theory.Frattini.PGroup
public import Mathlib.Tactic.ReduceModChar

/-!
# A concrete quaternion subgroup in the graph-field fixed group of PSL₃(4)

Two explicit determinant-one unitary matrices satisfy the quaternion
relations already in SL₃(4). Their common square is a transposition matrix,
whose projective class is nontrivial. Thus their projective images generate
an actual Q₈ contained in the graph-field fixed subgroup. Its intersection
with the centralizer of the displayed E₉ is trivial: every nonidentity
quaternion element generates the common involution, and that involution
does not commute with the displayed three-cycle.

A second explicit determinant-one matrix has Hermitian Gram matrix equal
to this involution. It provides the graph-field fusion identity required
when the intrinsic calculation is embedded in an ambient group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.4(5) and the centerless case of 16.4.9(2), pp.1171, 1191–1192.
The displayed matrices give the elementary unitary calculation directly.
-/

@[expose] public section

open Subgroup
namespace Matrix.PSL3Four.InnerFamilyNormalizer.Centerless
open ProjectiveGraphField
noncomputable section
set_option linter.unusedSimpArgs false
private theorem omega_sq : omega ^ 2 = omega + 1 := by
  have hp : (omega - 1) * (omega ^ 2 + omega + 1) = 0 := by
    calc
      _ = omega ^ 3 - 1 := by ring
      _ = 0 := by rw [omega_cube, sub_self]
  have hs := (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr omega_ne_one)
  apply add_right_cancel (b := omega + 1)
  calc
    omega ^ 2 + (omega + 1) = 0 := by simpa only [add_assoc] using hs
    _ = (omega + 1) + (omega + 1) := (CharTwo.add_self_eq_zero _).symm

def iSL : SL := ⟨!![omega^2,omega,1;omega,omega^2,1;1,1,1], by
  have hchar : CharP F 2 := inferInstance
  simp [Matrix.det_fin_three, omega_sq, CharTwo.sub_eq_add]
  ring_nf
  reduce_mod_char!⟩
def jSL : SL := ⟨!![omega^2,omega,omega;omega,omega^2,omega;omega^2,omega^2,1], by
  have hchar : CharP F 2 := inferInstance
  simp [Matrix.det_fin_three, omega_sq, CharTwo.sub_eq_add]
  ring_nf
  reduce_mod_char!⟩
def vSL : SL := ⟨!![0,1,0;1,0,0;0,0,1], by
  simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩

lemma i_unitary : iSL ∈ ProjectiveGraphField.unitary := by
  have hchar : CharP F 2 := inferInstance
  apply (mem_unitary_iff _).mpr
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [iSL, Matrix.mul_apply, Fin.sum_univ_three, omega_sq] <;>
    ring_nf <;> reduce_mod_char! <;> simp [omega_cube, pow_four, omega_sq] <;> ring_nf <;> reduce_mod_char!
lemma j_unitary : jSL ∈ ProjectiveGraphField.unitary := by
  have hchar : CharP F 2 := inferInstance
  apply (mem_unitary_iff _).mpr
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jSL, Matrix.mul_apply, Fin.sum_univ_three, omega_sq] <;>
    ring_nf <;> reduce_mod_char! <;> simp [omega_cube, pow_four, omega_sq] <;> ring_nf <;> reduce_mod_char!
lemma i_sq : iSL^2 = vSL := by
  have hchar : CharP F 2 := inferInstance
  apply Subtype.ext
  change iSL.val^2 = vSL.val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [iSL,vSL,pow_two, Matrix.mul_apply, Fin.sum_univ_three, omega_sq] <;>
    ring_nf <;> reduce_mod_char! <;> simp [omega_cube, pow_four, omega_sq] <;> ring_nf <;> reduce_mod_char!
lemma j_sq : jSL^2 = vSL := by
  have hchar : CharP F 2 := inferInstance
  apply Subtype.ext
  change jSL.val^2 = vSL.val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jSL,vSL,pow_two, Matrix.mul_apply, Fin.sum_univ_three, omega_sq] <;>
    ring_nf <;> reduce_mod_char! <;> simp [omega_cube, pow_four, omega_sq] <;> ring_nf <;> reduce_mod_char!
lemma v_sq : vSL^2 = 1 := by
  have hchar : CharP F 2 := inferInstance
  apply Subtype.ext
  change vSL.val^2 = (1 : Matrix (Fin 3) (Fin 3) F)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vSL,pow_two, Matrix.mul_apply, Fin.sum_univ_three]
lemma ji : jSL*iSL = vSL*iSL*jSL := by
  have hchar : CharP F 2 := inferInstance
  apply Subtype.ext
  change jSL.val*iSL.val = vSL.val*iSL.val*jSL.val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [iSL,jSL,vSL, Matrix.mul_apply, Fin.sum_univ_three, omega_sq] <;>
    ring_nf <;> reduce_mod_char!

open ExtendedCentralizer

def i : PSL := ProjectiveFixer.project iSL
def j : PSL := ProjectiveFixer.project jSL
def v : PSL := ProjectiveFixer.project vSL

theorem i_sq_projective : i ^ 2 = v := by
  rw [i, ← map_pow, i_sq]
  rfl

theorem j_sq_projective : j ^ 2 = v := by
  rw [j, ← map_pow, j_sq]
  rfl

theorem v_sq_projective : v ^ 2 = 1 := by
  rw [v, ← map_pow, v_sq, map_one]

theorem v_ne_one : v ≠ 1 := by
  intro h
  have hz : vSL ∈ center SL := (QuotientGroup.eq_one_iff _).mp h
  obtain ⟨r, _, he⟩ := SpecialLinearGroup.mem_center_iff.mp hz
  have hh := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 0 1) he
  exact zero_ne_one hh

theorem v_order : orderOf v = 2 := orderOf_eq_prime v_sq_projective v_ne_one

theorem i_order : orderOf i = 4 := by
  have hn : i ^ 2 ≠ 1 := by rw [i_sq_projective]; exact v_ne_one
  have h4 : i ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, i_sq_projective, v_sq_projective]
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using hn) (by simpa using h4)

theorem j_conj_i : j * i * j⁻¹ = i⁻¹ := by
  have h : j * i = v * i * j := by
    change ProjectiveFixer.project jSL * ProjectiveFixer.project iSL =
      ProjectiveFixer.project vSL * ProjectiveFixer.project iSL * ProjectiveFixer.project jSL
    simp only [← map_mul]
    exact congrArg ProjectiveFixer.project ji
  rw [h, mul_assoc, mul_inv_cancel, mul_one, ← i_sq_projective]
  apply eq_inv_of_mul_eq_one_right
  have h4 : i ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, i_sq_projective, v_sq_projective]
  simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using h4

theorem j_not_zpowers_i : j ∉ zpowers i := by
  rintro ⟨k, hk⟩
  have hcomm : j * i * j⁻¹ = i := by rw [← hk]; group
  have hai : i = i⁻¹ := hcomm.symm.trans j_conj_i
  apply v_ne_one
  rw [← i_sq_projective, pow_two]
  exact (congrArg (· * i) hai).trans (inv_mul_cancel i)

/-- A concrete quaternion subgroup of the projective graph-field fixed group. -/
def quaternion : Subgroup PSL := Subgroup.closure ({i, j} : Set PSL)

theorem quaternion_card : Nat.card quaternion = 8 :=
  (QuaternionGroup.closure_equiv_of_relations (m := 2) (by decide) i j i_order
    (j_sq_projective.trans i_sq_projective.symm) j_conj_i j_not_zpowers_i).1

theorem quaternion_equiv : Nonempty (quaternion ≃* QuaternionGroup 2) :=
  (QuaternionGroup.closure_equiv_of_relations (m := 2) (by decide) i j i_order
    (j_sq_projective.trans i_sq_projective.symm) j_conj_i j_not_zpowers_i).2

theorem quaternion_le_fixed : quaternion ≤ ProjectiveFixer.graphField.fixedSubgroup := by
  apply (Subgroup.closure_le _).mpr
  rintro x (rfl | rfl)
  · exact (fixedProjection (⟨iSL, i_unitary⟩ : ProjectiveGraphField.unitary)).property
  · exact (fixedProjection (⟨jSL, j_unitary⟩ : ProjectiveGraphField.unitary)).property


theorem i_mem_quaternion : i ∈ quaternion := Subgroup.subset_closure (by simp)
theorem j_mem_quaternion : j ∈ quaternion := Subgroup.subset_closure (by simp)
theorem v_mem_quaternion : v ∈ quaternion :=
  i_sq_projective ▸ quaternion.pow_mem i_mem_quaternion 2

theorem quaternion_isTwoGroup : IsPGroup 2 quaternion :=
  IsPGroup.of_card (p := 2) (n := 3) (by simpa using quaternion_card)

theorem v_mem_frattini : v ∈ (frattini quaternion).map quaternion.subtype := by
  let : Fact (IsPGroup 2 quaternion) := ⟨quaternion_isTwoGroup⟩
  exact ⟨(⟨i, i_mem_quaternion⟩ : quaternion) ^ 2,
    pth_power_mem_frattini_of_isPGroup (p := 2) _, i_sq_projective⟩

theorem quaternion_disjoint_model : Disjoint quaternion ProjectiveFixer.model :=
  Subgroup.disjoint_of_coprime_natCard (by
    rw [quaternion_card, ProjectiveFixer.model_card]
    decide)

private theorem quaternion_eight_squares : ∀ a b : QuaternionGroup 2,
    a ≠ 1 → a ^ 2 = 1 → b ≠ 1 → b = a ∨ b ^ 2 = a := by
  decide +kernel

theorem quaternion_nonidentity (x : PSL) (hx : x ∈ quaternion) (hne : x ≠ 1) :
    x = v ∨ x ^ 2 = v := by
  obtain ⟨e⟩ := quaternion_equiv
  let vv : quaternion := ⟨v, v_mem_quaternion⟩
  let xx : quaternion := ⟨x, hx⟩
  have hvne : e vv ≠ 1 := by
    intro h
    have hh := e.injective (h.trans (map_one e).symm)
    exact v_ne_one (congrArg Subtype.val hh)
  have hv2 : (e vv) ^ 2 = 1 := by
    rw [← map_pow, show vv ^ 2 = 1 from Subtype.ext v_sq_projective, map_one]
  have hxne : e xx ≠ 1 := by
    intro h
    have hh := e.injective (h.trans (map_one e).symm)
    exact hne (congrArg Subtype.val hh)
  rcases quaternion_eight_squares (e vv) (e xx) hvne hv2 hxne with h | h
  · exact Or.inl (congrArg Subtype.val (e.injective h))
  · rw [← map_pow] at h
    exact Or.inr (congrArg Subtype.val (e.injective h))

theorem v_not_centralizer_model : v ∉ centralizer (ProjectiveFixer.model : Set PSL) := by
  intro hv
  have hc := (mem_centralizer_iff.mp hv) ProjectiveFixer.cycle
    ProjectiveFixer.cycle_mem_model
  have he : ProjectiveFixer.project (vSL * ProjectiveFixer.cycleSL) =
      ProjectiveFixer.project (ProjectiveFixer.cycleSL * vSL) := by
    simpa only [map_mul, v, ProjectiveFixer.cycle] using hc.symm
  obtain ⟨r, _, he⟩ := (ProjectiveFixer.project_eq_iff _ _).mp he
  have hh := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 0 2) he
  change (vSL.val * ProjectiveFixer.cycleSL.val) 0 2 =
    (Matrix.scalar (Fin 3) r * (ProjectiveFixer.cycleSL.val * vSL.val)) 0 2 at hh
  simp [vSL, ProjectiveFixer.cycleSL, Matrix.mul_apply, Fin.sum_univ_three] at hh

theorem quaternion_inf_centralizer_model :
    quaternion ⊓ centralizer (ProjectiveFixer.model : Set PSL) = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 1
  by_contra hne
  rcases quaternion_nonidentity x hx.1 hne with h | h
  · exact v_not_centralizer_model (h ▸ hx.2)
  · exact v_not_centralizer_model (h ▸ (centralizer (ProjectiveFixer.model : Set PSL)).pow_mem hx.2 2)

def fusionSL : SL := ⟨!![1,1,0;omega,omega^2,0;0,0,1], by
  have hchar : CharP F 2 := inferInstance
  simp [Matrix.det_fin_three, omega_sq, CharTwo.sub_eq_add]
  ring_nf
  reduce_mod_char!⟩

theorem fusionSL_gram :
    fusionSL * SpecialLinearGroup.transpose (slFrobenius fusionSL) = vSL := by
  have hchar : CharP F 2 := inferInstance
  apply Subtype.ext
  change fusionSL.val * (slFrobenius fusionSL).val.transpose = vSL.val
  have hf : (slFrobenius fusionSL).val = fusionSL.val.map (fun x => x ^ 2) := by
    ext r c
    exact slFrobenius_apply fusionSL r c
  rw [hf]
  change (!![1,1,0;omega,omega^2,0;0,0,1] : Matrix (Fin 3) (Fin 3) F) *
    ((!![1,1,0;omega,omega^2,0;0,0,1] : Matrix (Fin 3) (Fin 3) F).map
      (fun x => x ^ 2)).transpose = !![0,1,0;1,0,0;0,0,1]
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, omega_sq] <;>
    ring_nf <;> reduce_mod_char! <;> simp [omega_cube, pow_four, omega_sq] <;>
    ring_nf <;> reduce_mod_char!

theorem exists_fusion : ∃ s : PSL, s * ProjectiveFixer.graphField (s⁻¹) = v := by
  refine ⟨ProjectiveFixer.project fusionSL, ?_⟩
  have hh : slAction (fusionSL⁻¹) = SpecialLinearGroup.transpose (slFrobenius fusionSL) := by
    rw [map_inv, slAction_apply, inv_inv]
  change ProjectiveFixer.project fusionSL * ProjectiveFixer.project (slAction (fusionSL⁻¹)) =
    ProjectiveFixer.project vSL
  rw [hh, ← map_mul, fusionSL_gram]

end
end Matrix.PSL3Four.InnerFamilyNormalizer.Centerless
