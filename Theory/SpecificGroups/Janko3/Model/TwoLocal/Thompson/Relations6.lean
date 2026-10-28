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

public theorem power_relation_6 : gen 6 ^ radix 6 =
    representative 6 (powerIndex 6) := by
  apply Subtype.ext
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem conjugate_relation_6 (i : Fin 6) :
    gen 6 * gen i.val * (gen 6)⁻¹ = representative (conjugateDepth 6 i.val) (conjugateIndex 6 i.val) := by
  have h : ∀ i : Fin 6, ∀ x : Fin 6156,
      ((gen 6 * gen i.val * (gen 6)⁻¹ : Model) : Equiv.Perm (Fin 6156)) x =
      ((representative (conjugateDepth 6 i.val) (conjugateIndex 6 i.val) : Model) :
        Equiv.Perm (Fin 6156)) x := by
    apply allFin₂
    decide +kernel
  exact Subtype.ext (Equiv.ext (h i))

public theorem inverse_conjugate_relation_6 (i : Fin 6) :
    (gen 6)⁻¹ * gen i.val * gen 6 = representative (conjugateDepth 6 i.val) (inverseConjugateIndex 6 i.val) := by
  have h : ∀ i : Fin 6, ∀ x : Fin 6156,
      (((gen 6)⁻¹ * gen i.val * gen 6 : Model) : Equiv.Perm (Fin 6156)) x =
      ((representative (conjugateDepth 6 i.val) (inverseConjugateIndex 6 i.val) : Model) :
        Equiv.Perm (Fin 6156)) x := by
    apply allFin₂
    decide +kernel
  exact Subtype.ext (Equiv.ext (h i))

end Sporadic.Janko3.TwoLocal.ThompsonCertificate
