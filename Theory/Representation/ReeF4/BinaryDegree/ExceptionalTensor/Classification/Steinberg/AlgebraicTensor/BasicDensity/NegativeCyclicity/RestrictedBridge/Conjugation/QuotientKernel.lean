module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge.Conjugation.Basic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge.Conjugation.QuotientKernel.FiniteKernels
public import Theory.AlgebraicGroup.Bor1.ConjugationRational
public import Theory.AlgebraicGroup.Bor1.NormalWeights
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Theory.AlgebraicGroup.Semisimple.Versions

/-!
# Conjugation preserves the simple quotient action's kernel

The actual quotient action is surjective onto its full endomorphism algebra.
Its twists by root-algebra conjugations therefore have only finitely many
kernels, by the Artinian-ring argument in `FiniteKernels`. Embed the kernel in
the original factor's endomorphism space. Conjugation there is a rational
representation, so its subspace stabilizer is closed. Connectedness of the
F₄ carrier then makes this finite subspace orbit a singleton.

This proves preservation of the annihilator of the actual simple quotient,
not preservation of the kernel of its projection from the cyclic module.
Root-algebra normalization remains the explicit input `RootConjugationStable`.
The proof uses only the connectedness part of universality and the rationality
part of the original factor's irreducibility; it needs no highest-line theorem,
restricted-module classification, or rational action on the quotient.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), equation 4.1 and the equivalence with the twisted module preceding
4.2; DOI 10.1017/S0027763000011016. The connected finite-orbit argument provides
an independent proof of the kernel assertion needed for that equivalence.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

omit [IsAlgClosed F] in
private theorem end_isSimpleRing (V : Type u) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Nontrivial V] : IsSimpleRing (Module.End F V) := by
  have : Nonempty (Fin (Module.finrank F V)) := ⟨⟨0, Module.finrank_pos⟩⟩
  exact IsSimpleRing.of_ringEquiv
    (LinearMap.toMatrixAlgEquiv (Module.finBasis F V)).symm.toRingEquiv inferInstance

namespace SimpleCyclicQuotient
variable {B : AlgebraicFactor F} {v : B.Space} (Q : SimpleCyclicQuotient B v)

private theorem conjugate_kernel_map (hs : RootConjugationStable B) (g : PointGroup F) :
    Submodule.map (rootConjugate B hs g).toLinearMap (LinearMap.ker Q.rootAction.toLinearMap) =
      LinearMap.ker (Q.rootAction.comp (rootConjugate B hs g).symm.toAlgHom).toLinearMap := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    change Q.rootAction ((rootConjugate B hs g).symm (rootConjugate B hs g x)) = 0
    rw [AlgEquiv.symm_apply_apply]
    exact hx
  · intro ha
    exact ⟨(rootConjugate B hs g).symm a, ha, (rootConjugate B hs g).apply_symm_apply a⟩

/-- The action annihilator has finite orbit under the restricted conjugations. -/
theorem rootAction_kernel_finite_orbit (hs : RootConjugationStable B) :
    (Set.range fun g : PointGroup F =>
      Submodule.map (rootConjugate B hs g).toLinearMap
        (LinearMap.ker Q.rootAction.toLinearMap)).Finite := by
  have : IsSimpleRing (Module.End F Q.Space) := end_isSimpleRing Q.Space
  simp_rw [Q.conjugate_kernel_map hs]
  exact QuotientKernel.finite_range_linear_kernels
    (fun g => Q.rootAction.comp (rootConjugate B hs g).symm.toAlgHom)
    (fun g => Q.rootAction_surjective.comp (rootConjugate B hs g).symm.surjective)

/-- Every actual group conjugation preserves the annihilator of the simple
quotient. Together with `implementer_of_kernel`, this gives equivalence of the
quotient with its twist, once root-algebra normalization is supplied. -/
theorem rootAction_rootConjugate_eq_zero_iff
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (hs : RootConjugationStable B) (g : PointGroup F) (a : rootAlgebra B) :
    Q.rootAction (rootConjugate B hs g a) = 0 ↔ Q.rootAction a = 0 := by
  let K : Submodule F (rootAlgebra B) := LinearMap.ker Q.rootAction.toLinearMap
  let inc : rootAlgebra B →ₗ[F] Module.End F B.Space := (rootAlgebra B).val.toLinearMap
  let W : Submodule F (Module.End F B.Space) := K.map inc
  let rho := Bor1.conjEndRationalRepresentation B.action
  have hmap (x : PointGroup F) :
      Submodule.map (rho.action x : Module.End F (Module.End F B.Space)) W =
        (K.map (rootConjugate B hs x).toLinearMap).map inc := by
    change (K.map inc).map _ = _
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    rfl
  have hfinite : (Set.range fun x : PointGroup F =>
      Submodule.map (rho.action x : Module.End F (Module.End F B.Space)) W).Finite := by
    simp_rw [hmap]
    exact (Q.rootAction_kernel_finite_orbit hs).image (fun L => L.map inc) |>.subset
      (by rintro _ ⟨x, rfl⟩; exact ⟨_, ⟨x, rfl⟩, rfl⟩)
  have hinv : ∀ x : PointGroup F,
      Submodule.map (rho.action x : Module.End F (Module.End F B.Space)) W = W :=
    Bor1.Representation.subspace_invariant_of_connected_of_finite_orbit
      ((Units.coeHom _).comp rho.action) W hU.1.1
      (Bor1.RationalRepresentation.subspaceStabilizer_isZariskiClosed_Bor1 rho
        (Bor1.conjEndRationalRepresentation_isRational B.action B.irreducible.1) W) hfinite
  have hK (x : PointGroup F) : K.map (rootConjugate B hs x).toLinearMap = K := by
    apply Submodule.map_injective_of_injective (f := inc) Subtype.val_injective
    rw [← hmap, hinv]
  have hmem : rootConjugate B hs g a ∈ K ↔ a ∈ K := by
    nth_rw 1 [← hK g]
    constructor
    · rintro ⟨x, hx, he⟩
      exact (rootConjugate B hs g).injective he ▸ hx
    · intro ha
      exact ⟨a, ha, rfl⟩
  exact hmem

end SimpleCyclicQuotient
end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
