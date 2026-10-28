module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ConjugateSection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Basic
public import Theory.Representation.Quotient

/-!
# Intrinsic module data at the conjugate endpoint

The actual quotient isomorphism H/O₂(H) → Hᵍ/O₂(Hᵍ) transports the invariant
subspace lattice. Its inverse pulls the action back while retaining the
vector coordinates. The maximal submodule, its natural head and the chosen
natural-or-dual irreducible therefore retain the same compatible linear
identifications. Images of actual conjugate subgroups agree with these
coordinates through `conjugateSection`.

These are intrinsic transports. They make no assertion about common centers
or axes for the swapped actor, which need the source nonsplitting argument.
The normalized graph pair has the original base H again, so its original
submodules can be used after the geometric and subgroup identities are checked.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Remark F.9.17,
printed p.324, as applied to 13.8.25, printed p.962.
-/

@[expose] public section

open Subgroup Representation
open CFSG.Quasithin.Chapter13.Section08
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
  {H UH Z : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) U}

/-- The lattice transport uses the actual endpoint quotient isomorphism. -/
noncomputable def endpointLattice (e : G ≃* G) (ρ : Representation (ZMod 2) (Source.Hstar H) U) :
    Subrepresentation ρ ≃o
      Subrepresentation (ρ.comp (starEquiv e H).symm.toMonoidHom) :=
  (Representation.inflationSubrepresentationOrderIso (starEquiv e H).symm.toMonoidHom
    (starEquiv e H).symm.surjective ρ).symm

theorem endpointLattice_submodule (e : G ≃* G) (W : Subrepresentation ρ) :
    (endpointLattice e ρ W).toSubmodule = W.toSubmodule := rfl

theorem endpointLattice_image (s : ConjugationSection H UH Z ρ)
    (e : G ≃* G) (I : Subgroup G) (N : Subrepresentation ρ)
    (hI : s.image I = N.toSubmodule) :
    (conjugateSection s e).image (I.map e.toMonoidHom) =
      (endpointLattice e ρ N).toSubmodule := by
  rw [conjugateSection_image, endpointLattice_submodule, hI]

theorem endpointLattice_isCoatom (e : G ≃* G) (W : Subrepresentation ρ) :
    IsCoatom (endpointLattice e ρ W) ↔ IsCoatom W :=
  (endpointLattice e ρ).isCoatom_iff W

theorem endpointLattice_isAtom (e : G ≃* G) (N : Subrepresentation ρ) :
    IsAtom (endpointLattice e ρ N) ↔ IsAtom N :=
  (endpointLattice e ρ).isAtom_iff N

theorem endpointLattice_ne_bot (e : G ≃* G) (W : Subrepresentation ρ) (hW : W ≠ ⊥) :
    endpointLattice e ρ W ≠ ⊥ := by
  intro h
  apply hW
  exact (endpointLattice e ρ).injective (h.trans (endpointLattice e ρ).map_bot.symm)

theorem endpointLattice_le (e : G ≃* G) (N W : Subrepresentation ρ) (h : N ≤ W) :
    endpointLattice e ρ N ≤ endpointLattice e ρ W :=
  (endpointLattice e ρ).monotone h

/-- The same linear equivalence identifies the head after the actual group
quotient isomorphism; no new GL₄(2) identification is chosen. -/
theorem endpointLattice_natural_head (e : G ≃* G) (W : Subrepresentation ρ)
    (eH : Source.Hstar H ≃* BinaryLinear.GL ChiefFactors.NaturalSpace)
    (hNat : ChiefFactors.IsNatural W.quotientRepresentation eH) :
    ChiefFactors.IsNatural (endpointLattice e ρ W).quotientRepresentation
      ((starEquiv e H).symm.trans eH) := by
  obtain ⟨f, hf⟩ := hNat
  exact ⟨f, fun a u => hf ((starEquiv e H).symm a) u⟩

theorem endpointLattice_natural_or_dual (e : G ≃* G) (N : Subrepresentation ρ)
    (eH : Source.Hstar H ≃* BinaryLinear.GL ChiefFactors.NaturalSpace)
    (hNat : ChiefFactors.IsNaturalOrDual N.toRepresentation eH) :
    ChiefFactors.IsNaturalOrDual (endpointLattice e ρ N).toRepresentation
      ((starEquiv e H).symm.trans eH) := by
  rcases hNat with ⟨f, hf⟩ | ⟨f, hf⟩
  · exact Or.inl ⟨f, fun a u => hf ((starEquiv e H).symm a) u⟩
  · refine Or.inr ⟨f, ?_⟩
    intro a u
    have hh := hf ((starEquiv e H).symm a) u
    rw [Representation.dual_apply] at hh ⊢
    change f (N.toRepresentation ((starEquiv e H).symm a) u) =
      (Module.Dual.transpose ((ChiefFactors.naturalAction eH)
        ((starEquiv e H).symm a⁻¹))) (f u)
    rw [map_inv]
    exact hh

theorem endpointLattice_irreducible (e : G ≃* G) (N : Subrepresentation ρ) :
    IsIrreducible (endpointLattice e ρ N).toRepresentation ↔
      IsIrreducible N.toRepresentation := by
  change IsIrreducible (N.toRepresentation.comp (starEquiv e H).symm.toMonoidHom) ↔ _
  exact irreducible_comp_surjective_iff _ (starEquiv e H).symm.surjective _

/-- Uniqueness of the maximal submodule is intrinsic and transports too. -/
theorem endpointLattice_unique_maximal (e : G ≃* G) (W : Subrepresentation ρ)
    (hW : ∀ X : Subrepresentation ρ, IsCoatom X → X = W) :
    ∀ X : Subrepresentation (ρ.comp (starEquiv e H).symm.toMonoidHom),
      IsCoatom X → X = endpointLattice e ρ W := by
  intro X hX
  obtain ⟨Y, rfl⟩ := (endpointLattice e ρ).surjective X
  exact congrArg (endpointLattice e ρ) (hW Y ((endpointLattice_isCoatom e Y).mp hX))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
