module

public import Theory.LinearAlgebra.BinarySymplecticSeven
public import Theory.LinearAlgebra.BinaryAlternatingFour

/-!
Conjugate a nonsingular alternating binary form to the standard symplectic form
and apply the checked order-seven obstruction. Conjugation preserves seventh
powers and reflects the identity. The nondegeneracy hypothesis is essential for
this reduction; singular forms are handled separately.
-/

public section

open Matrix

namespace BinarySymplecticSeven

theorem arbitrary_form_order_seven_eq_one (form actor : Mat)
    (halt : form.toBilin'.IsAlt) (hnondegenerate : form.toBilin'.Nondegenerate)
    (hpower : actor ^ 7 = 1)
    (hpres : actor.transpose * form * actor = form) : actor = 1 := by
  obtain ⟨standardActor, hstandard, hpowers, hidentity⟩ :=
    BinaryAlternatingFour.transport_preserving_actor form actor halt hnondegenerate hpres
  exact hidentity.mp (matrix_order_seven_eq_one standardActor (hpowers 7 hpower) hstandard)

end BinarySymplecticSeven
