module

public import Theory.Representation.BinaryOffender.MarkedCentralQuotient
public import Theory.Representation.BinaryDuadModule
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.G2NaturalBinary

/-!
# Actual natural coordinates for the three cases of 13.5.21

The alternatives retain an isomorphism of K*V* with S₆, A₈ or G₂(2)′,
the marked component, and an equivariant linear equivalence with the
concrete natural representation. They imply irreducibility on K* by the
proved natural-module calculations. No group-family tag or dimension alone
is used as recognition.

Source: Aschbacher–Smith, 13.5.21(2)–(3), printed p.924 (PDF p.941).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.CentralQuotient

variable {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]

/-- The source's natural coordinates, including the original component marking. -/
def NaturalAction (K : Subgroup E) (σ : Representation (ZMod 2) E W) : Prop :=
  (∃ (e : E ≃* Theory.SpecificGroups.SymmetricSix.S6)
      (f : W ≃ₗ[ZMod 2] Theory.SpecificGroups.SymmetricSix.NaturalModule),
    K.map e.toMonoidHom = Theory.SpecificGroups.SymmetricSix.A6 ∧
    ∀ g w, f (σ g w) = BinaryDuadModule.naturalAction (e g) (f w)) ∨
  (∃ (e : E ≃* alternatingGroup (Fin 8))
      (f : W ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8)),
    K = ⊤ ∧ ∀ g w, f (σ g w) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (e g) (f w)) ∨
  (∃ (e : E ≃* commutator (Atlas.G2.Model (ZMod 2)))
      (f : W ≃ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2)),
    K = ⊤ ∧ ∀ g w, f (σ g w) = g2DerivedNatural (ZMod 2) (e g) (f w))

private theorem irreducible_top_restriction
    {M X : Type*} [Group M] [AddCommGroup X] [Module (ZMod 2) X]
    (K : Subgroup E) (σ : Representation (ZMod 2) E W)
    (τ : Representation (ZMod 2) M X) (e : E ≃* M) (f : W ≃ₗ[ZMod 2] X)
    (hK : K = ⊤) (hf : ∀ g w, f (σ g w) = τ (e g) (f w))
    (hi : IsIrreducible τ) : IsIrreducible (σ.comp K.subtype) := by
  apply irreducible_of_surjective_equivariant _ τ (e.toMonoidHom.comp K.subtype) _ f
    (fun g w => hf g w) hi
  intro m
  obtain ⟨g, rfl⟩ := e.surjective m
  exact ⟨⟨g, hK.symm ▸ mem_top g⟩, rfl⟩

/-- The concrete natural modules are irreducible for the marked component. -/
theorem NaturalAction.component_irreducible {K : Subgroup E}
    {σ : Representation (ZMod 2) E W} (h : NaturalAction K σ) :
    IsIrreducible (σ.comp K.subtype) := by
  rcases h with ⟨e, f, hK, hf⟩ | ⟨e, f, hK, hf⟩ | ⟨e, f, hK, hf⟩
  · let q : K →* Theory.SpecificGroups.SymmetricSix.A6 :=
      (e.toMonoidHom.comp K.subtype).codRestrict _
        (fun k => hK ▸ mem_map_of_mem e.toMonoidHom k.property)
    have hq : Function.Surjective q := by
      intro a
      have ha : a.val ∈ K.map e.toMonoidHom := hK.symm ▸ a.property
      obtain ⟨k, hk, he⟩ := ha
      exact ⟨⟨k, hk⟩, Subtype.ext he⟩
    exact irreducible_of_surjective_equivariant _
      BinaryDuadModule.alternatingNaturalAction q hq f (fun k w => hf k w)
      BinaryDuadModule.alternatingNaturalAction_irreducible
  · exact irreducible_top_restriction K σ _ e f hK hf
      (BinaryPermutation.alternatingNatural_isIrreducible (by decide))
  · exact irreducible_top_restriction K σ _ e f hK hf
      Atlas.G2.Natural.Binary.natural_irreducible


end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.CentralQuotient
