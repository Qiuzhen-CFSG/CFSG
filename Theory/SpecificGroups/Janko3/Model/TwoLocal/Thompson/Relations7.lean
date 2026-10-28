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

public theorem power_relation_7 : gen 7 ^ radix 7 =
    representative 7 (powerIndex 7) := by
  apply Subtype.ext
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem conjugate_relation_7 (i : Fin 7) :
    gen 7 * gen i.val * (gen 7)⁻¹ = representative (conjugateDepth 7 i.val) (conjugateIndex 7 i.val) := by
  have h : ∀ i : Fin 7, ∀ x : Fin 6156,
      ((gen 7 * gen i.val * (gen 7)⁻¹ : Model) : Equiv.Perm (Fin 6156)) x =
      ((representative (conjugateDepth 7 i.val) (conjugateIndex 7 i.val) : Model) :
        Equiv.Perm (Fin 6156)) x := by
    apply allFin₂
    decide +kernel
  exact Subtype.ext (Equiv.ext (h i))

public theorem inverse_conjugate_relation_7 (i : Fin 7) :
    (gen 7)⁻¹ * gen i.val * gen 7 = representative (conjugateDepth 7 i.val) (inverseConjugateIndex 7 i.val) := by
  have h : ∀ i : Fin 7, ∀ x : Fin 6156,
      (((gen 7)⁻¹ * gen i.val * gen 7 : Model) : Equiv.Perm (Fin 6156)) x =
      ((representative (conjugateDepth 7 i.val) (inverseConjugateIndex 7 i.val) : Model) :
        Equiv.Perm (Fin 6156)) x := by
    apply allFin₂
    decide +kernel
  exact Subtype.ext (Equiv.ext (h i))

end Sporadic.Janko3.TwoLocal.ThompsonCertificate
