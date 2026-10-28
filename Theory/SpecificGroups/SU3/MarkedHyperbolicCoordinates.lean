module

public import Theory.SpecificGroups.SU3.ExceptionalQuaternionRotation
public import Theory.GroupTheory.CyclicByFourOuterInvolutions

/-!
# A marked unitary plane in cyclic-by-four coordinates

This interface retains the full unitary-plane homomorphism alongside the
four Sylow normal forms. The scalar, rotation and swap are identified with
their actual images, and the outer generator implements field conjugation
on the entire image. The image lies in the specified inner subgroup, which
allows transport through a faithful ambient action. Injectivity of the plane
map is not required: the projective ternary block map has an odd scalar kernel.

The interface does not mention a supplied cyclic core or exceptional pair.
Those are identified independently by cyclic-subgroup uniqueness and the
outer-involution dichotomy. Concrete model existence is a separate theorem.

Source application: Aschbacher--Smith E.1.14(7), printed p.214, and
Aschbacher (1982), Lemma 4.11; the inner Sylow shape is A.3.21(b), p.55.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory
namespace Matrix.UnitaryQuaternionRotation
variable {G F : Type*} [Group G] [Field F]

/-- The plane map and generator markings needed to transport the concrete
unitary Sylow calculation. This records no fusion or core-identification claim. -/
structure MarkedCyclicByFour (L T : Subgroup G) (z : G) (J : HermitianForm 2 F) where
  coordinates : CyclicByFourCoordinates L T z
  form_eq : J.form = !![0, 1; 1, 0]
  two_ne_zero : (2 : F) ≠ 0
  r : Fˣ
  r_conj : J.conj (r : F) = -(r : F)
  i : F
  i_sq : i ^ 2 = -1
  i_conj : J.conj i = i
  embedding : J.unitarySubgroup →* G
  embedding_inner : ∀ u, embedding u ∈ L
  marker_eq : embedding (minusOne J form_eq) = z
  rotation_eq : embedding (torus J form_eq r r_conj) = coordinates.a
  swap_eq : embedding (swap J form_eq) = coordinates.b
  actor_action : ∀ u, coordinates.c * embedding u * coordinates.c⁻¹ =
    embedding (fieldConj J form_eq u)

namespace MarkedCyclicByFour
variable {L T : Subgroup G} {z : G} {J : HermitianForm 2 F}

/-- The marked reflection is square-one because it is the actual coordinate swap. -/
theorem reflection_sq (q : MarkedCyclicByFour L T z J) : q.coordinates.b ^ 2 = 1 := by
  have hs : swap J q.form_eq ^ 2 = 1 := by
    apply Subtype.ext
    exact GeneralLinearGroup.coordinateSwap_sq F
  rw [← q.swap_eq, ← map_pow, hs, map_one]

end MarkedCyclicByFour
end Matrix.UnitaryQuaternionRotation
