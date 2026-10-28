module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.TransvectionSections.CoreQuotients
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.TransvectionSections.NaturalGeometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.TransvectionSections.SourceRecognition

/-!
# Compatible section models in the transvection branch of 13.8.25

The local sieve excludes only best strong offenders contained in the critical
actor and retains both positions of the critical line. Intrinsic involution
geometry proves rank one on either faithful section, and 13.8.23's dimension
argument gives fixed codimension one on both.

The transposition centers construct an equivariant map from the augmentation
core onto the actual commutator [W,K]. Its invariant kernel gives the natural
six-dimensional or augmentation seven-dimensional model inside W. A single
coordinate change identifies the actor with the transposition group while
transporting both section models and the alternating component.

`source_compatible_sections` applies this to the literal U_H/V₁ conjugation
module, using the independently supplied maximal submodule, natural quotient
and earlier critical-pair inputs. It retains the actual critical subgroup and
both containment alternatives, and discharges the core-map and rank-one
obligations. The earlier conditional core-map interface remains available
below. Final offender-alternative and orthogonal-exclusion assembly belongs
to the parent task.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.25, printed p.960 (PDF p.977), using 13.8.22–23 and B.3.1.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.TransvectionSections
open Representation.BinaryOffender Subgroup BinaryPermutation
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

/-- Construct the same permutation marking for the quotient, actor, component,
and actual commutator submodule. The map from the augmentation core is an
explicit construction input, not an assumed section-model identification. -/
theorem compatible_sections_of_core_map
    (ρ : Representation (ZMod 2) H U) (W : Subrepresentation ρ)
    (K : Subgroup H) (eH : H ≃* Perm)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hQ : IsEightNatural W.quotientRepresentation eH)
    (A : Subgroup H) (hA : IsElementaryTwo A)
    (hcQ : fixedCodim W.quotientRepresentation A = 1)
    (f : core (Fin 8) →ₗ[ZMod 2] W.toSubmodule)
    (heq : ∀ g v, f (coreRepresentation (Fin 8) (eH g) v) = W.toRepresentation g (f v))
    (hrange : LinearMap.range f = subspaceCommutator W.toRepresentation ⊤ K)
    (hKW : ∃ k ∈ K, ∃ w : W.toSubmodule, W.toRepresentation k w ≠ w) :
    rank A = 1 ∧ ∃ g : Perm, ∃ J : Subrepresentation W.toRepresentation,
      A.map (conjugateMarking eH g).toMonoidHom = transpositionGroup ∧
      K.map (conjugateMarking eH g).toMonoidHom = alternatingGroup (Fin 8) ∧
      IsEightNatural W.quotientRepresentation (conjugateMarking eH g) ∧
      J.toSubmodule = subspaceCommutator W.toRepresentation ⊤ K ∧
      IsEightNaturalOrCover J.toRepresentation (conjugateMarking eH g) := by
  have hJ := commutator_model_of_core_map W.toRepresentation K eH f heq hrange hKW
  obtain ⟨hr, g, hg, _⟩ := codim_one_actor_marking W.quotientRepresentation eH (Or.inl hQ) A hA hcQ
  obtain ⟨J, hJcomm, hJmodel⟩ := commutator_model_conjugate W.toRepresentation K eH hJ g
  exact ⟨hr, g, J, hg, alternating_marking_conjugate eH K hK g,
    IsEightNatural.conjugate W.quotientRepresentation eH hQ g, hJcomm, hJmodel⟩
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.TransvectionSections
