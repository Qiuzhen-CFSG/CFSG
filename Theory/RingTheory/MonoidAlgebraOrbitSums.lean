module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Group.Action.End
public import Theory.RingTheory.FiniteInvariantSeparation
public import Theory.Representation.PermutationBasisOrbitSums
public import Mathlib.Algebra.Module.Submodule.EqLocus
/-!
# Distinct weight-orbit sums separate torus points

The character lattice acts as the monomial basis of its group algebra.
A finite group of lattice automorphisms permutes that basis. Invariant
polynomials are therefore spanned by distinct orbit sums, and agreement on
all these sums puts two torus evaluations in the same finite-group orbit.
This holds in arbitrary characteristic, including characteristic two.

Source: Steinberg (1963), §3.9. Reducing this full separating family to the
four fundamental-weight sums remains the next Ree source step.
-/

open scoped BigOperators
open Module
public noncomputable section
namespace Theory.MonoidAlgebraOrbitSums
variable {F G L : Type*} [Field F] [Group G] [CommGroup L]
  [MulDistribMulAction G L]
@[expose] noncomputable def algebraAction : G →* (MonoidAlgebra F L ≃ₐ[F] MonoidAlgebra F L) :=
  (MonoidAlgebra.domCongrAut (R := F) (A := F)).comp (MulDistribMulAction.toMulAut G L)
@[instance_reducible] private noncomputable def weightAlgebraAction : MulSemiringAction G (MonoidAlgebra F L) :=
  MulSemiringAction.compHom _ (algebraAction (F := F) (G := G) (L := L))
attribute [local instance] weightAlgebraAction

private theorem weightAlgebraComm : SMulCommClass G F (MonoidAlgebra F L) :=
  ⟨fun g c p => (algebraAction (F := F) (L := L) g).toLinearEquiv.map_smul c p⟩

attribute [local instance] weightAlgebraComm

private lemma smul_basis (g : G) (i : L) :
    g • (MonoidAlgebra.basis L F) i = (MonoidAlgebra.basis L F) (g • i) := by
  change MonoidAlgebra.domCongr F F (MulDistribMulAction.toMulEquiv L g)
    (MonoidAlgebra.single i 1) = _
  rw [MonoidAlgebra.domCongr_single]
  rfl

@[expose] noncomputable def pointEvaluation (t : L →* Fˣ) : MonoidAlgebra F L →ₐ[F] F :=
  MonoidAlgebra.lift F F L ((Units.coeHom F).comp t)

lemma pointEvaluation_basis (t : L →* Fˣ) (i : L) :
    pointEvaluation t ((MonoidAlgebra.basis L F) i) = (t i : F) := by
  simp [pointEvaluation, MonoidAlgebra.basis_apply]

variable [Finite G]

/-- Reindexing by a lattice automorphism fixes each distinct orbit sum. -/
theorem algebraAction_orbitSum (g : G) (i : L) :
    algebraAction (F := F) g (PermutationBasisOrbitSums.orbitSum (G := G)
      (MonoidAlgebra.basis L F) i) =
      PermutationBasisOrbitSums.orbitSum (G := G) (MonoidAlgebra.basis L F) i :=
  PermutationBasisOrbitSums.smul_orbitSum (MonoidAlgebra.basis L F) smul_basis g i

/-- The sum of character values over a distinct lattice orbit. -/
@[expose] def orbitSumValue (t : L →* Fˣ) (i : L) : F :=
  pointEvaluation t (PermutationBasisOrbitSums.orbitSum (G := G)
    (MonoidAlgebra.basis L F) i)

/-- All distinct character-orbit sums separate finite orbits of torus points. -/
theorem exists_smul_of_orbitSumValue_eq (t s : L →* Fˣ)
    (heq : ∀ i : L, orbitSumValue (G := G) t i = orbitSumValue (G := G) s i) :
    ∃ g : G, ∀ i : L, s i = t (g • i) := by
  have hinv : ∀ p : MonoidAlgebra F L, (∀ g : G, g • p = p) →
      pointEvaluation t p = pointEvaluation s p := by
    intro p hp
    have hm := PermutationBasisOrbitSums.invariant_mem_span_orbitSum
      (MonoidAlgebra.basis L F) smul_basis p hp
    have hle : Submodule.span F (Set.range (PermutationBasisOrbitSums.orbitSum
        (G := G) (MonoidAlgebra.basis L F))) ≤
        LinearMap.eqLocus (pointEvaluation t).toLinearMap
          (pointEvaluation s).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact heq i
    exact hle hm
  obtain ⟨g, hg⟩ := FiniteInvariantSeparation.exists_smul_of_eq_on_invariants
    (pointEvaluation t) (pointEvaluation s) hinv
  refine ⟨g, fun i => Units.ext ?_⟩
  simpa only [smul_basis, pointEvaluation_basis] using
    hg ((MonoidAlgebra.basis L F) i)

end Theory.MonoidAlgebraOrbitSums
