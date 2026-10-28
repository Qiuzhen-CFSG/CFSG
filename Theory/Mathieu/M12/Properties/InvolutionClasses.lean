module

public import Mathlib.Algebra.Group.Fin.Basic
public import Theory.Mathieu.M12.Basic

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Sporadic.Mathieu

public noncomputable def m12AInvolution : M12 :=
  ⟨m12GeneratorA, m12GeneratorA_mem⟩

public noncomputable def m12BElement : M12 :=
  ⟨m12GeneratorB, m12GeneratorB_mem⟩

/-! The Atlas `2A` representative `(a b a b a b b)^3`. -/
@[expose]
public noncomputable def m12Involution2A : M12 :=
  (m12AInvolution * m12BElement * m12AInvolution * m12BElement *
    m12AInvolution * m12BElement * m12BElement) ^ 3

/-! The Atlas `2B` representative, the first standard generator. -/
@[expose]
public noncomputable def m12Involution2B : M12 := m12AInvolution

public theorem m12Involution2A_order : orderOf m12Involution2A = 2 := by
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

public theorem m12Involution2B_order : orderOf m12Involution2B = 2 := by
  rw [m12Involution2B, ← Subgroup.orderOf_coe]
  exact m12GeneratorA_order

public theorem m12Involution2A_support_card :
    ((m12Involution2A : Equiv.Perm (Fin 12)).support.card) = 12 := by
  change
    (((m12GeneratorA * m12GeneratorB * m12GeneratorA * m12GeneratorB *
      m12GeneratorA * m12GeneratorB * m12GeneratorB) ^ 3).support.card) = 12
  decide +kernel

public theorem m12Involution2B_support_card :
    ((m12Involution2B : Equiv.Perm (Fin 12)).support.card) = 8 := by
  change (m12GeneratorA.support.card) = 8
  decide +kernel

public theorem m12Involution2A_ne_2B : m12Involution2A ≠ m12Involution2B := by
  intro h
  have hs := congrArg (fun g : M12 => (g : Equiv.Perm (Fin 12)).support.card) h
  rw [m12Involution2A_support_card, m12Involution2B_support_card] at hs
  omega

end Sporadic.Mathieu
