module

public import Theory.Representation.BinaryPermutation.OddOffenderTransport
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Fixed-space comparison from an actual natural summand

An equivariant inclusion and retraction, with trivial complementary action,
identify the quotient by every fixed space with the corresponding quotient
of the natural module. This proves equality of fixed codimensions through
the literal permutation homomorphism, even when the whole module is larger.

`NaturalSummand` is a linear splitting interface, not a source hypothesis or
a proof of its own existence. The ordinary A₇ application must construct it
from the chosen block model, the U_K identification, and the seed span.
Its restriction to K⁺ can also serve as the input to the independent
normalizer-extension argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.3.3(1),
printed p.84, and its use in 13.6.22, printed p.932.
-/

@[expose] public section

open Subgroup Equiv
open Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison
variable {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]

/-- An actual natural summand with a pointwise fixed complement. -/
structure NaturalSummand (ρ : Representation (ZMod 2) H V) (φ : H →* Perm (Fin 7)) where
  inclusion : BinaryPermutation.natural (Fin 7) →ₗ[ZMod 2] V
  projection : V →ₗ[ZMod 2] BinaryPermutation.natural (Fin 7)
  retraction : ∀ w, projection (inclusion w) = w
  inclusion_equivariant : ∀ g w, ρ g (inclusion w) =
    inclusion (BinaryPermutation.naturalRepresentation (Fin 7) (φ g) w)
  projection_equivariant : ∀ g w, projection (ρ g w) =
    BinaryPermutation.naturalRepresentation (Fin 7) (φ g) (projection w)
  remainder_fixed : ∀ g w, ρ g (w - inclusion (projection w)) = w - inclusion (projection w)

variable {ρ : Representation (ZMod 2) H V} {φ : H →* Perm (Fin 7)}

theorem NaturalSummand.inclusion_injective (d : NaturalSummand ρ φ) :
    Function.Injective d.inclusion := by
  intro v w h
  simpa only [d.retraction] using congrArg d.projection h

theorem NaturalSummand.fixedSpace_preimage (d : NaturalSummand ρ φ) (A : Subgroup H) :
    (fixedSpace (BinaryPermutation.naturalRepresentation (Fin 7)) (A.map φ)).comap
      d.projection = fixedSpace ρ A := by
  ext v
  constructor
  · intro hv a
    have h := d.remainder_fixed a.val v
    have hv' : BinaryPermutation.naturalRepresentation (Fin 7) (φ a.val)
        (d.projection v) = d.projection v := hv ⟨φ a.val, mem_map_of_mem φ a.property⟩
    rw [map_sub, d.inclusion_equivariant, hv'] at h
    exact sub_left_inj.mp h
  · intro hv
    rintro ⟨_, a, ha, rfl⟩
    exact (d.projection_equivariant a v).symm.trans (congrArg d.projection (hv ⟨a, ha⟩))

theorem NaturalSummand.fixedCodim_eq (d : NaturalSummand ρ φ) (A : Subgroup H) :
    fixedCodim ρ A = fixedCodim (BinaryPermutation.naturalRepresentation (Fin 7)) (A.map φ) := by
  let F := fixedSpace (BinaryPermutation.naturalRepresentation (Fin 7)) (A.map φ)
  let f := F.mkQ.comp d.projection
  have hf : Function.Surjective f := (Submodule.mkQ_surjective F).comp
    (fun w => ⟨d.inclusion w, d.retraction w⟩)
  have hk : f.ker = fixedSpace ρ A := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    exact d.fixedSpace_preimage A
  exact ((Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hf)).finrank_eq

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison

end
