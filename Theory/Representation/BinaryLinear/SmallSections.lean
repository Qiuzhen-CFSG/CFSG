module

public import Theory.Representation.BinaryLinear.CubicFixedSpace
public import Theory.Representation.BinaryPermutation.CubicFixedSpace.Five

/-!
# Small central sections with a Sylow fixed-space obstruction

Two concrete restrictions admit cubic fixed-space witnesses: an embedded
GL₄(𝔽₂) acting through natural and dual modules, and an embedded A₅ acting
through its four-dimensional natural permutation section. The restriction
has a submodule with central kernel over that model and a trivial quotient.
All embeddings and action-intertwining maps are retained explicitly.

These predicates describe sufficient module structures. No assertion that
an arbitrary FF-module has either structure is made here. Their construction
for the binary automorphism groups is the remaining representation step in
Aschbacher–Smith, 15.4.20, printed p.1164; compare B.5.1, printed p.99.
-/

@[expose] public section
namespace Representation.BinaryLinearSections
open Subgroup BinaryOffender
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]

/-- A restriction to an actual embedded GL₄(𝔽₂), with a natural/dual
central section. Neither the kernel nor the outer extension need split. -/
def HasNaturalDualSection (ρ : Representation (ZMod 2) D V) : Prop :=
  ∃ f : BinaryLinear.FourFixedSpace.Actor →* D, Function.Injective f ∧
    ∃ (a b : ℕ) (U : Subrepresentation (ρ.comp f))
      (q : U.toSubmodule →ₗ[ZMod 2]
        ((Fin a → BinaryLinear.FourFixedSpace.Space) ×
          (Fin b → Module.Dual (ZMod 2) BinaryLinear.FourFixedSpace.Space))),
      (∀ g u, q (U.toRepresentation g u) = BinaryLinear.FourFixedSpace.copies a b g (q u)) ∧
      (∀ g u, q u = 0 → U.toRepresentation g u = u) ∧
      (∀ g v, ρ (f g) v - v ∈ U)

/-- A restriction to an actual embedded A₅, with its natural binary
permutation section between a central kernel and a trivial quotient. -/
def HasAlternatingFiveSection (ρ : Representation (ZMod 2) D V) : Prop :=
  ∃ f : alternatingGroup (Fin 5) →* D, Function.Injective f ∧
    ∃ (U : Subrepresentation (ρ.comp f))
      (q : U.toSubmodule →ₗ[ZMod 2] BinaryPermutation.natural (Fin 5)),
      (∀ g u, q (U.toRepresentation g u) =
        BinaryPermutation.naturalRepresentation (Fin 5) g.val (q u)) ∧
      (∀ g u, q u = 0 → U.toRepresentation g u = u) ∧
      (∀ g v, ρ (f g) v - v ∈ U)

/-- Either of the two explicitly compatible central-section structures. -/
def HasSmallSection (ρ : Representation (ZMod 2) D V) : Prop :=
  HasNaturalDualSection ρ ∨ HasAlternatingFiveSection ρ

/-- Every specified small section produces a cubic element outside the
given Sylow subgroup fixing its whole fixed space. -/
theorem HasSmallSection.sylow_enlargement [Finite D]
    (ρ : Representation (ZMod 2) D V) (h : HasSmallSection ρ) (S : Sylow 2 D) :
    ∃ c : D, c ∉ S ∧ c ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ c v = v := by
  rcases h with ⟨f, hf, a, b, U, q, hq, hker, hquot⟩ | ⟨f, hf, U, q, hq, hker, hquot⟩
  · exact BinaryLinear.FourFixedSpace.centralSection_enlargement
      ρ f hf a b U q hq hker hquot S
  · exact BinaryPermutation.CubicFixedSpace.Five.centralSection_enlargement
      ρ f hf U q hq hker hquot S

end Representation.BinaryLinearSections
