module

public import Theory.SpecificGroups.Janko3.Model.ThreePrimary.Data
import Mathlib.Tactic.FinCases

/-!
# Checked Sylow-three collection equations

Every power and conjugation equation below is verified on all 6156 letters.
The separating-letter inverse is checked on 243 normal forms. Thus the
structural conclusions use no trusted GAP calculation or presentation claim.
Source: GLS III, Table 5.3h; original ATLAS J3 permutation data.
-/

namespace Sporadic.Janko3.ThreePrimary
open Theory.GroupTheory OrderCertificate
open scoped commutatorElement
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option Elab.async false

public theorem power_relation (k : Fin 5) :
    gen k.val ^ 3 = representative k.val (powerCode k) := by
  fin_cases k <;> apply Subtype.ext <;> apply Equiv.ext <;>
    apply allLetters <;> decide +kernel

public theorem conjugate_relation (k : Fin 5) (i : Fin k.val) :
    gen k.val * gen i.val * (gen k.val)⁻¹ =
      representative k.val (conjugateCode k.val i.val) := by
  fin_cases k <;> fin_cases i <;> apply Subtype.ext <;> apply Equiv.ext <;>
    apply allLetters <;> decide +kernel

public theorem inverse_conjugate_relation (k : Fin 5) (i : Fin k.val) :
    (gen k.val)⁻¹ * gen i.val * gen k.val =
      representative k.val (inverseConjugateCode k.val i.val) := by
  fin_cases k <;> fin_cases i <;> apply Subtype.ext <;> apply Equiv.ext <;>
    apply allLetters <;> decide +kernel

public theorem representative_point_inverse : ∀ r : Fin 243,
    pointInverse ((representative 5 r.val : Equiv.Perm (Fin 6156)) separatingPoint) = r := by
  apply allFin
  decide +kernel

public theorem c_cube : c ^ 3 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem x_cube : x ^ 3 = d ^ 2 * e := by
  apply Subtype.ext
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem y_cube : y ^ 3 = d ^ 2 * e ^ 2 := by
  apply Subtype.ext
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem d_commute_x : Commute d x := by
  apply Subtype.ext
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem d_commute_y : Commute d y := by
  apply Subtype.ext
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem e_commute_x : Commute e x := by
  apply Subtype.ext
  apply Equiv.ext
  apply allLetters
  decide +kernel

public theorem e_commute_y : Commute e y := by
  apply Subtype.ext
  apply Equiv.ext
  apply allLetters
  decide +kernel

end Sporadic.Janko3.ThreePrimary
