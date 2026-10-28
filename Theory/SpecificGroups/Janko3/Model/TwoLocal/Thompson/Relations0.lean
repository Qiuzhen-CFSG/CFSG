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

public theorem power_relation_0 : gen 0 ^ radix 0 =
    representative 0 (powerIndex 0) := by
  apply Subtype.ext
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem conjugate_relation_0 (i : Fin 0) :
    gen 0 * gen i.val * (gen 0)⁻¹ = representative (conjugateDepth 0 i.val) (conjugateIndex 0 i.val) := by
  exact Fin.elim0 i

public theorem inverse_conjugate_relation_0 (i : Fin 0) :
    (gen 0)⁻¹ * gen i.val * gen 0 = representative (conjugateDepth 0 i.val) (inverseConjugateIndex 0 i.val) := by
  exact Fin.elim0 i

end Sporadic.Janko3.TwoLocal.ThompsonCertificate
