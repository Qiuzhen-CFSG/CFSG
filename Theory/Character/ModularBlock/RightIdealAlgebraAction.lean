module

public import Theory.Character.ModularBlock.IsotypicLattice

/-!
# Right Ideal Algebra Action

The group-algebra action associated to the regular right-ideal
representation agrees with left multiplication on its underlying image.
The proof checks basis elements and extends linearly. This identifies the
representation action used in characterwise arguments with the right-ideal
endomorphism whose trace is computed by the isotypic-lattice API.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/CharacterwiseNagao.lean` (revision `c3503435`).
-/

public section

noncomputable section

open scoped BigOperators

namespace ModularBlock.IsotypicLattice

open ModularBlock PrincipalBlockConstruction

universe u

attribute [local instance] Fintype.ofFinite

/-- The regular right-ideal action really is left multiplication by the
corresponding group-algebra element. -/
theorem rightIdealRepresentation_asAlgebraHom_apply
    {R : Type*} {G : Type*} [CommRing R] [Group G]
    (q a : MonoidAlgebra R G)
    (x : CentralIdempotentSupport.rightIdeal R q) :
    ((CentralIdempotentSupport.rightIdealRepresentation R q).asAlgebraHom a x :
        MonoidAlgebra R G) =
      a * (x : MonoidAlgebra R G) := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
      rw [map_add, LinearMap.add_apply]
      change
        ((CentralIdempotentSupport.rightIdealRepresentation R q).asAlgebraHom a x :
            MonoidAlgebra R G) +
          ((CentralIdempotentSupport.rightIdealRepresentation R q).asAlgebraHom b x :
            MonoidAlgebra R G) =
          (a + b) * (x : MonoidAlgebra R G)
      rw [ha, hb, add_mul]
  | single g r =>
      rw [show (MonoidAlgebra.single g r : MonoidAlgebra R G) =
        r • MonoidAlgebra.single g 1 by simp, map_smul,
        Representation.asAlgebraHom_single_one]
      change r • (MonoidAlgebra.of R G g * (x : MonoidAlgebra R G)) =
        (r • MonoidAlgebra.of R G g) * (x : MonoidAlgebra R G)
      exact (Algebra.smul_mul_assoc r _ _).symm

theorem rightIdealRepresentation_asAlgebraHom
    {R : Type*} {G : Type*} [CommRing R] [Group G]
    (q a : MonoidAlgebra R G) :
    (CentralIdempotentSupport.rightIdealRepresentation R q).asAlgebraHom a =
      IsotypicLattice.rightIdealLeftMul q a := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact rightIdealRepresentation_asAlgebraHom_apply q a x


end ModularBlock.IsotypicLattice

