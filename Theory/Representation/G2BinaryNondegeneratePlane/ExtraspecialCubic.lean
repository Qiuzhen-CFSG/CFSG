module

public import Theory.Representation.G2BinaryNondegeneratePlane.Stabilizer
public import Theory.Representation.FirstCohomologyG2Natural.BinaryPair
public import Theory.GroupTheory.PGroup.HeisenbergPair
import Mathlib.Tactic.ReduceModChar

/-!
# A noncentral cubic in an actual extraspecial subgroup of G₂(2)′

The pointwise stabilizer of the marked nondegenerate plane contains a cubic.
An explicit word in two octonion commutators forms a Heisenberg pair with it.
Their six-dimensional actions verify the relations; the abstract prime-cube
pair theorem then proves order 27 and extraspeciality without a group census.

This supplies the concrete subgroup for the binary chief-factor obstruction in
Aschbacher–Smith 13.3.12, printed p.890. The imported octonion and root models
retain their ATLAS attribution.
-/

@[expose] public section

open scoped commutatorElement MatrixGroups
open Subgroup Matrix
namespace Atlas.G2.Natural.BinaryNondegeneratePlane
open Atlas.G2.Restricted.NaturalCoordinates

theorem cubic_mem_derived : cubic∈commutator (Model K) := by
  let u : SL(2,K) := ⟨!![1,1;0,1],by decide⟩
  let s : SL(2,K) := ⟨!![0,1;1,0],by decide⟩
  have h : cubicMatrix=⁅u,s⁆ := by decide +kernel
  rw [cubic,h,map_commutatorElement]
  exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)

def derivedCubic : commutator (Model K) := ⟨cubic,cubic_mem_derived⟩

def cubicPartner : commutator (Model K) :=
  binaryB K * binaryA K * binaryB K * (binaryA K)^3 * binaryB K * (binaryA K)^3

private theorem action_a (v : W) :
    rho (binaryA K).val v=![v 0+v 2+v 5,v 1+v 3+v 4+v 5,v 2+v 4,v 3+v 5,v 4,v 5] := by
  ext i
  fin_cases i <;> simp [action_apply,Atlas.G2.Restricted.NaturalCoordinates.projection,
    representative,traceZeroAction_val,binaryA_apply]
private theorem action_b (v : W) :
    rho (binaryB K).val v=![v 3,v 5,v 1,v 4,v 0,v 2] := by
  ext i
  fin_cases i <;> simp [action_apply,Atlas.G2.Restricted.NaturalCoordinates.projection,
    representative,traceZeroAction_val,binaryB_apply]

theorem cubicPartner_action (v : W) :
    rho cubicPartner.val v=![v 1+v 3+v 4,v 0+v 1+v 2+v 3+v 5,
      v 0+v 2+v 3+v 4,v 0+v 1+v 4,v 1+v 2+v 3+v 5,v 1+v 2+v 4] := by
  simp only [cubicPartner,Subgroup.coe_mul,map_mul,pow_succ,
    pow_zero,Module.End.mul_apply,action_a,action_b]
  ext i
  fin_cases i <;> simp <;> ring_nf
  all_goals
    have : CharP K 2 := inferInstance
    reduce_mod_char!

theorem cubicPartner_cube : cubicPartner^3=1 := by
  apply Subtype.ext
  apply rho_injective
  apply LinearMap.ext
  intro v
  simp only [Subgroup.coe_pow,Subgroup.coe_one,map_one,Module.End.one_apply]
  rw [map_pow]
  change rho cubicPartner.val (rho cubicPartner.val (rho cubicPartner.val v))=v
  simp only [cubicPartner_action]
  ext i
  fin_cases i <;> simp <;> ring_nf
  all_goals
    have : CharP K 2 := inferInstance
    reduce_mod_char!

def cubicCommutator : commutator (Model K) := ⁅derivedCubic,cubicPartner⁆

private theorem cubicCommutator_word :
    cubicCommutator=derivedCubic*cubicPartner*derivedCubic^2*cubicPartner^2 := by
  have hx : derivedCubic^3=1 := Subtype.ext cubic_cubed
  have hx' : derivedCubic⁻¹=derivedCubic^2 := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [←pow_succ'] using hx
  have hy' : cubicPartner⁻¹=cubicPartner^2 := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [←pow_succ'] using cubicPartner_cube
  simp only [cubicCommutator,commutatorElement_def,hx',hy']

theorem cubicCommutator_action (v : W) :
    rho cubicCommutator.val v=![v 5,v 3,v 4,v 1+v 3,v 2+v 4,v 0+v 5] := by
  simp only [cubicCommutator_word,Subgroup.coe_mul,derivedCubic,
    map_mul,pow_succ,pow_zero,Module.End.mul_apply,
    cubic_action,cubicPartner_action]
  ext i
  fin_cases i <;> simp <;> ring_nf
  all_goals
    have : CharP K 2 := inferInstance
    reduce_mod_char!

theorem cubicCommutator_cube : cubicCommutator^3=1 := by
  apply Subtype.ext
  apply rho_injective
  apply LinearMap.ext
  intro v
  simp only [Subgroup.coe_pow,Subgroup.coe_one,map_one,Module.End.one_apply]
  rw [map_pow]
  change rho cubicCommutator.val (rho cubicCommutator.val (rho cubicCommutator.val v))=v
  simp only [cubicCommutator_action]
  ext i
  fin_cases i <;> simp <;> ring_nf
  all_goals
    have : CharP K 2 := inferInstance
    reduce_mod_char!

theorem cubicCommutator_commute_cubic : Commute cubicCommutator derivedCubic := by
  apply Subtype.ext
  apply rho_injective
  apply LinearMap.ext
  intro v
  simp only [Subgroup.coe_mul,map_mul,Module.End.mul_apply,derivedCubic,
    cubic_action,cubicCommutator_action]
  ext i
  fin_cases i <;> simp
  all_goals ring

theorem cubicCommutator_commute_partner : Commute cubicCommutator cubicPartner := by
  apply Subtype.ext
  apply rho_injective
  apply LinearMap.ext
  intro v
  simp only [Subgroup.coe_mul,map_mul,Module.End.mul_apply,
    cubicPartner_action,cubicCommutator_action]
  ext i
  fin_cases i <;> simp <;> ring_nf
  all_goals
    have : CharP K 2 := inferInstance
    reduce_mod_char!

theorem cubic_pair_not_commute : derivedCubic*cubicPartner≠cubicPartner*derivedCubic := by
  intro he
  have hc : cubicCommutator=1 := commutatorElement_eq_one_iff_mul_comm.mpr he
  have h := cubicCommutator_action firstVector
  rw [hc,Subgroup.coe_one,map_one] at h
  exact one_ne_zero (congrFun h 0)

def cubicExtraspecial : Subgroup (commutator (Model K)) := closure {derivedCubic,cubicPartner}
theorem card_cubicExtraspecial : Nat.card cubicExtraspecial=3^3 :=
  PrimeCubePair.card_closure_pair derivedCubic cubicPartner
    (Subtype.ext cubic_cubed) cubicPartner_cube cubicCommutator_cube
    cubicCommutator_commute_cubic cubicCommutator_commute_partner cubic_pair_not_commute

theorem cubicExtraspecial_isExtraspecial : IsExtraspecial 3 cubicExtraspecial := by
  apply IsExtraspecial.of_noncommutative_card_prime_cube card_cubicExtraspecial
  intro h
  let := h
  let x : cubicExtraspecial := ⟨derivedCubic,subset_closure (by simp)⟩
  let y : cubicExtraspecial := ⟨cubicPartner,subset_closure (by simp)⟩
  have he : x*y=y*x := IsMulCommutative.is_comm.comm x y
  have he' := congrArg cubicExtraspecial.subtype he
  exact cubic_pair_not_commute he'

theorem cubic_noncentral :
    (⟨derivedCubic,subset_closure (by simp)⟩:cubicExtraspecial)∉center cubicExtraspecial := by
  intro h
  let y : cubicExtraspecial := ⟨cubicPartner,subset_closure (by simp)⟩
  exact cubic_pair_not_commute (congrArg Subtype.val (mem_center_iff.mp h y).symm)
end Atlas.G2.Natural.BinaryNondegeneratePlane
