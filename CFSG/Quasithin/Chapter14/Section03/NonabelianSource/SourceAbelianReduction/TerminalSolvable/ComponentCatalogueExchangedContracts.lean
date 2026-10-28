module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogue
public import Theory.Representation.NormalComponentConstituents

/-!
# Structural interface for a faithful exchanged constituent

The interface records the literal representation-theoretic assertions of
G.10.15(2)(II): the component orbit acts faithfully, the constituent is not
self-dual and is totally isotropic, and every distinct X-conjugate is its dual.
It contains neither a group-model identification nor the non-GL assertion.

The central-kernel branch must construct this data and prove the non-GL
assertion. The faithful G.11.6 recognition may consume them independently.
The exchanged-image assembly remains responsible for discharging both inputs.

Source: Aschbacher--Smith G.10.15(2)(II) and G.11.6, printed pp.361--363,366.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable

/-- The representation-theoretic data of G.10.15(2)(II), on the literal
component orbit and original exchanged subspaces. No group-model
identification or non-GL assertion is built into this interface. -/
@[expose] def ExchangedFaithfulConstituentData
    {D E : Type*} [Group D] [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) D E) (B : LinearMap.BilinForm (ZMod 2) E)
    (L X : Subgroup D) (I : Submodule (ZMod 2) E)
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I) : Prop :=
  let H := componentOrbit L ⊤
  letI := componentOrbit_top_normal L
  let R := invariantSubspace ρ H I hI.invariant
  Function.Injective R.toRepresentation.asGroupHom ∧
  ¬ Nonempty (Representation.Equiv R.toRepresentation R.toRepresentation.dual) ∧
  (∀ u ∈ I, ∀ w ∈ I, B u w = 0) ∧
  ∀ x : X, I.map (ρ (x : D)) ≠ I →
    Nonempty (Representation.Equiv R.toRepresentation
      (conjugateSubrepresentation ρ H R (x : D)).toRepresentation.dual)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
