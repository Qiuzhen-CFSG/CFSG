module

public import Theory.Mathieu.M24.Properties.InvolutionClasses

/-!
# Marked involution centralizers in the Witt-design M₂₄

The two certified permutations are regarded as elements of M₂₄ itself.
Their centralizers below are full centralizers in that carrier. These definitions
make no assertion about class coverage or the structures of the centralizers.

Source: Aschbacher–Smith 16.1.5(7), printed p.1171; GLS3, Table 5.3e.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24InvolutionCentralizers

noncomputable def involution2A : M24 := ⟨m24Involution2A, m24Involution2A_mem⟩
noncomputable def involution2B : M24 := ⟨m24Involution2B, m24Involution2B_mem⟩

noncomputable abbrev centralizer2A := Subgroup.centralizer ({involution2A} : Set M24)
noncomputable abbrev centralizer2B := Subgroup.centralizer ({involution2B} : Set M24)

theorem involution2A_order : orderOf involution2A = 2 :=
  (Subgroup.orderOf_coe involution2A).symm.trans m24Involution2A_order

theorem involution2B_order : orderOf involution2B = 2 :=
  (Subgroup.orderOf_coe involution2B).symm.trans m24Involution2B_order

end Sporadic.Mathieu.M24InvolutionCentralizers
