module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.KernelCharacteristic
public import Theory.SpecificGroups.PSL3Two.Parabolics.OrderTwentyFour

/-!
# A marked symmetric-four quotient above the same native kernel

Restrict the actual PSL3(2) quotient to a subgroup of order3072 containing
its full kernel. Its image has order24, hence is a symmetric-four
parabolic. The resulting surjection keeps exactly the original kernel.
-/

public noncomputable section
open Subgroup
namespace Sporadic.Mathieu.M24InvolutionCentralizers.TwoA

/-- The native order3072 subgroup has a symmetric-four quotient with its
full original kernel, not merely an abstract section. -/
theorem parabolic_symmetricFour_quotient (H : Subgroup centralizer2A)
    (hKH : kernel≤H) (hH : Nat.card H=3072) :
    ∃ q : H→*Equiv.Perm (Fin 4), Function.Surjective q ∧ q.ker=kernel.subgroupOf H := by
  let f : centralizer2A→*Matrix.PSL3Two.PSL :=
    quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' kernel)
  have hk : f.ker=kernel := by
    rw [MonoidHom.ker_comp_of_injective _ _ quotientEquiv.injective,QuotientGroup.ker_mk']
  have hc : Nat.card (H.map f)=24 := by
    have hh := IsElementaryAbelian.card_inf_ker_mul_card_map H f
    rw [hk,inf_eq_right.mpr hKH,kernel_card,hH] at hh
    omega
  obtain ⟨e⟩ := Matrix.PSL3Two.subgroup_twentyFour_equiv_symmetric (H.map f) hc
  let q := e.toMonoidHom.comp (f.subgroupMap H)
  refine ⟨q,e.surjective.comp (f.subgroupMap_surjective H),?_⟩
  rw [show q=e.toMonoidHom.comp (f.subgroupMap H) from rfl,
    MonoidHom.ker_comp_of_injective _ _ e.injective,ker_subgroupMap,hk]

end Sporadic.Mathieu.M24InvolutionCentralizers.TwoA
