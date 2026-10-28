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

public theorem power_relation_3 : gen 3 ^ radix 3 =
    representative 3 (powerIndex 3) := by
  apply Subtype.ext
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem conjugate_relation_3 (i : Fin 3) :
    gen 3 * gen i.val * (gen 3)⁻¹ = representative (conjugateDepth 3 i.val) (conjugateIndex 3 i.val) := by
  have h : ∀ i : Fin 3, ∀ x : Fin 6156,
      ((gen 3 * gen i.val * (gen 3)⁻¹ : Model) : Equiv.Perm (Fin 6156)) x =
      ((representative (conjugateDepth 3 i.val) (conjugateIndex 3 i.val) : Model) :
        Equiv.Perm (Fin 6156)) x := by
    apply allFin₂
    decide +kernel
  exact Subtype.ext (Equiv.ext (h i))

public theorem inverse_conjugate_relation_3 (i : Fin 3) :
    (gen 3)⁻¹ * gen i.val * gen 3 = representative (conjugateDepth 3 i.val) (inverseConjugateIndex 3 i.val) := by
  have h : ∀ i : Fin 3, ∀ x : Fin 6156,
      (((gen 3)⁻¹ * gen i.val * gen 3 : Model) : Equiv.Perm (Fin 6156)) x =
      ((representative (conjugateDepth 3 i.val) (inverseConjugateIndex 3 i.val) : Model) :
        Equiv.Perm (Fin 6156)) x := by
    apply allFin₂
    decide +kernel
  exact Subtype.ext (Equiv.ext (h i))

end Sporadic.Janko3.TwoLocal.ThompsonCertificate
