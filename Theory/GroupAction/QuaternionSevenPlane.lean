module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Hom.Defs

/-!+# A marked seven-plane with quaternion conjugations

This interface records an embedded elementary abelian group of order 49 and
two actual ambient elements inducing the specified quaternion matrices. It
does not assume any representation-degree conclusion or subgroup catalogue.

The intended construction uses a nonsplit torus in the genuine triality
group at q = 2. Its binary representation application also uses the scalar
Frobenius action on characters. The two constructions share this marking so
that the conjugation and character-pullback conventions cannot drift.

Source motivation: ATLAS, triality group at q = 2, printed p.89; the concrete
construction and the representation bound require separate proofs.
-/

public section
namespace QuaternionSevenPlane

abbrev Plane := ZMod 7 × ZMod 7

@[expose] def firstMap (z : Plane) : Plane := (4 * z.2, 5 * z.1)

@[expose] def secondMap (z : Plane) : Plane :=
  (2 * z.1 + 5 * z.2, 6 * z.1 + 5 * z.2)

theorem firstMap_sq : ∀ z : Plane, firstMap (firstMap z) = -z := by decide

theorem secondMap_sq : ∀ z : Plane, secondMap (secondMap z) = -z := by decide

theorem maps_anticommute :
    ∀ z : Plane, firstMap (secondMap z) = -secondMap (firstMap z) := by decide

/-- The maps are conjugation by the displayed ambient elements, not their
inverses. Character actions consequently use inverse pullback. -/
structure Data (G : Type*) [Group G] where
  embedding : Multiplicative Plane →* G
  embedding_injective : Function.Injective embedding
  first : G
  second : G
  first_conjugation : ∀ z : Plane,
    first * embedding (Multiplicative.ofAdd z) * first⁻¹ =
      embedding (Multiplicative.ofAdd (firstMap z))
  second_conjugation : ∀ z : Plane,
    second * embedding (Multiplicative.ofAdd z) * second⁻¹ =
      embedding (Multiplicative.ofAdd (secondMap z))

end QuaternionSevenPlane
