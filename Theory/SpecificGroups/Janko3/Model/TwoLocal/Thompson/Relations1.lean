module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson.Data

/-!
# Certified power and conjugation relations at one stage of the J₃ series

Each permutation equality is checked by kernel reduction on all 6156 letters.
Source: the concrete ATLAS model; GLS 3, Table 5.3h, printed p.269.
-/

namespace Sporadic.Janko3.TwoLocal.ThompsonCertificate
open OrderCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option Elab.async false

public theorem power_relation_1 : gen 1 ^ radix 1 =
    representative 1 (powerIndex 1) := by
  apply Subtype.ext
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem conjugate_relation_1 (i : Fin 1) :
    gen 1 * gen i.val * (gen 1)⁻¹ = representative (conjugateDepth 1 i.val) (conjugateIndex 1 i.val) := by
  have h : ∀ i : Fin 1, ∀ x : Fin 6156,
      ((gen 1 * gen i.val * (gen 1)⁻¹ : Model) : Equiv.Perm (Fin 6156)) x =
      ((representative (conjugateDepth 1 i.val) (conjugateIndex 1 i.val) : Model) :
        Equiv.Perm (Fin 6156)) x := by
    apply allFin₂
    decide +kernel
  exact Subtype.ext (Equiv.ext (h i))

public theorem inverse_conjugate_relation_1 (i : Fin 1) :
    (gen 1)⁻¹ * gen i.val * gen 1 = representative (conjugateDepth 1 i.val) (inverseConjugateIndex 1 i.val) := by
  have h : ∀ i : Fin 1, ∀ x : Fin 6156,
      (((gen 1)⁻¹ * gen i.val * gen 1 : Model) : Equiv.Perm (Fin 6156)) x =
      ((representative (conjugateDepth 1 i.val) (inverseConjugateIndex 1 i.val) : Model) :
        Equiv.Perm (Fin 6156)) x := by
    apply allFin₂
    decide +kernel
  exact Subtype.ext (Equiv.ext (h i))

end Sporadic.Janko3.TwoLocal.ThompsonCertificate
