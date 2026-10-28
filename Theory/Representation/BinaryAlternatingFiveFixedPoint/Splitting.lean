module
public import Theory.Representation.ProjectiveIsotypicComplementAction
public import Theory.Representation.BinaryAlternatingNaturalCohomology.Injective
public import Theory.Representation.BinaryAlternatingFiveFixedPoint.Orbit
public import Theory.Alternating.Aut

/-!
# The canonical deleted A₅ summand

The binary deleted core is both projective and injective, and every A₅
automorphism is induced by a permutation of the five coordinates. Its full
isotypic component therefore has a canonical complement preserved by every
compatible normalizing actor, without assuming semisimplicity of the target.

Source: Aschbacher--Smith I.1.6 and the whole-layer step of 5.1.19,
printed pp.408,643--644. This splitting removes the obstruction to applying
the Borel fixed-point argument to the entire reduced module.
-/

@[expose] public noncomputable section
open scoped MonoidAlgebra
open Representation Module
namespace Representation.BinaryAlternatingFiveFixedPoint
open BinaryPermutation

/-- The deleted core is invariant under every automorphism twist of A₅. -/
theorem core_twist (a : MulAut A5) :
    ∃ c : core (Fin 5) ≃ₗ[ZMod 2] core (Fin 5), ∀ g v,
      c (alternatingCoreRepresentation (Fin 5) g v) =
        alternatingCoreRepresentation (Fin 5) (a g) (c v) := by
  obtain ⟨p, hp⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    5 (by decide) (by decide)).surjective a
  let σ := coreRepresentation (Fin 5)
  let C := LinearEquiv.ofBijective (σ p) (σ.apply_bijective p)
  refine ⟨C, ?_⟩
  intro g v
  have he : (a g : Equiv.Perm (Fin 5)) = p * g.val * p⁻¹ :=
    (congrArg (fun f : MulAut A5 => (f g).val) hp).symm
  change σ p (σ g.val v) = σ (a g).val (σ p v)
  rw [he]
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- No ambient semisimplicity is needed for the deleted A₅ splitting. -/
theorem isCompl_core_typeSpan_typeReject [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) A5 V) :
    IsCompl (typeSpan ρ (alternatingCoreRepresentation (Fin 5)))
      (typeReject ρ (alternatingCoreRepresentation (Fin 5))) := by
  let : Module.Injective (ZMod 2)[A5] (alternatingCoreRepresentation (Fin 5)).asModule :=
    alternatingFive_core_injective
  let : Module.Projective (ZMod 2)[A5] (alternatingCoreRepresentation (Fin 5)).asModule :=
    alternatingFive_core_projective
  let e : alternatingCoreRepresentation (Fin 5) ≃ₗ alternatingNaturalRepresentation (Fin 5) :=
    .mk (coreEquivNatural (Fin 5) (by decide)) (by
      intro g
      apply LinearMap.ext
      intro v
      exact coreEquivNatural_equivariant (Fin 5) (by decide) g.val v)
  let : (alternatingCoreRepresentation (Fin 5)).IsIrreducible :=
    e.irreducible_of_euqiv (alternatingNatural_isIrreducible (by decide))
  exact isCompl_typeSpan_typeReject ρ _
end Representation.BinaryAlternatingFiveFixedPoint
