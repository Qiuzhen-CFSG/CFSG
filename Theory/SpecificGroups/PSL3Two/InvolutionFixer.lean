module
public import Theory.SpecificGroups.PSL3Two.InvolutionResidual

/-!
# Automorphisms fixing an involution of SL₃(2)

The outer automorphism quotient and the centralizer of an involution are
two-groups. Raising a fixing automorphism to a two-power makes it inner;
its inner representative centralizes the involution, so a further two-power
kills it. Consequently every two-perfect action fixing that involution is
trivial. This applies to the literal core quotient of a binary SL₃ block.

Source application: Aschbacher--Smith 15.1.24(2), printed p.1101.
-/

public section
open Subgroup
namespace Matrix.PSL3Two.InvolutionResidual

/-- The automorphisms fixing a specified involution form a two-group. -/
theorem automorphism_stabilizer_two (v : SL) (hv : orderOf v = 2) :
    IsPGroup 2 (MulAction.stabilizer (MulAut SL) v) := by
  let F := MulAction.stabilizer (MulAut SL) v
  intro a
  obtain ⟨j,hj⟩ := Automorphisms.outer_sl_isTwoGroup
    (QuotientGroup.mk' (MulAut.innerSubgroup SL) (a : MulAut SL))
  have hi : (a : MulAut SL) ^ (2 ^ j) ∈ MulAut.innerSubgroup SL := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (MulAut.innerSubgroup SL) (a : MulAut SL)) ^ (2 ^ j) = 1 at hj
    rw [←map_pow] at hj
    exact hj
  obtain ⟨g,hg⟩ := hi
  have hf : ((a : MulAut SL) ^ (2 ^ j)) v = v :=
    show ((a : MulAut SL) ^ (2 ^ j)) ∈ F from F.pow_mem a.property _
  rw [←hg,MulAut.conj_apply] at hf
  have hc : g ∈ centralizer ({v} : Set SL) :=
    mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hf)
  obtain ⟨k,hk⟩ := sl_centralizer_two v hv ⟨g,hc⟩
  have hk' : g ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  refine ⟨j + k,Subtype.ext ?_⟩
  change (a : MulAut SL) ^ (2 ^ (j+k)) = 1
  rw [pow_add,pow_mul,←hg,←map_pow,hk',map_one]

/-- A two-perfect automorphism action fixing an involution is trivial. -/
theorem action_eq_one_of_fixed_involution {Y : Type*} [Group Y]
    (hY : IsPPerfect 2 Y) (f : Y →* MulAut SL) (v : SL)
    (hv : orderOf v = 2) (hfix : ∀ y, f y v = v) : f = 1 := by
  let g := f.codRestrict (MulAction.stabilizer (MulAut SL) v) hfix
  have hg := hY.hom_eq_one_of_isPGroup (automorphism_stabilizer_two v hv) g
  apply MonoidHom.ext
  intro y
  exact congrArg (fun j : Y →* MulAction.stabilizer (MulAut SL) v => (j y).val) hg

end Matrix.PSL3Two.InvolutionResidual
