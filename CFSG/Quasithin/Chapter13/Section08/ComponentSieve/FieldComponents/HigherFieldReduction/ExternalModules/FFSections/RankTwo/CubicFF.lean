module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.CubicFF.Constituents
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.CubicFF.CentralSplitting
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.CubicFF.PairSaturation

/-!
# Intrinsic cubic FF actions with an odd-degree PSL₃ component

A faithful binary action with the normal odd-degree PSL₃ component and the
commuting marked S₃ action is not strong FF. If it is FF, the canonical
inverter-fixed multiplicity of the literal full moved section [V,K]/0 is
natural or binary dual-natural under the original component marking.

Quadratic replacement gives a minimal best offender. The constituent sieve
excludes motion on the cubic group and recognizes a stabilized Irr⁺ central
quotient, with ratio 1/2. Vanishing natural first cohomology removes the central
kernel. Its actual dimension 3n is odd, so its cubic conjugate is disjoint.
The two equal codimensions pay the offender's full rank, excluding strong FF.
For FF, equality forces K to centralize the quotient by this pair, so the pair
is exactly [V,K]. Its canonical multiplicity coordinates retain both natural
orientations and the literal zero bottom. An ambient K-central complement is
permitted.

The only classification inputs are the complete universal B.4.2 and B.1.5(3)
implications. Central splitting, odd dimension, pairing, saturation and natural
coordinates are all derived here from the structural hypotheses.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.2,
F.9.18(6), I.1.5–6 and the proof of 13.8.20(a), printed pp.954–955.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
open InvertedCubicTensor
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NoStrongMoved

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.CubicFF
universe u v
variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal] [IsQuasisimple K]
  {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦) (hInv : FullIrrInvariance.{u,v})
  (hS : IsSQTK 𝒦 D) (hf : Function.Injective ρ)
  (X : Subgroup D) [X.Normal] (hx : Nat.card X = 3)
  (hc : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
  (s : S₃ →* D) (hs : ∀ (k : K) g, Commute (k : D) (s g))
  (hmark : (alternatingGroup (Fin 3)).map s = X)
  (hg : subspaceCommutator ρ ⊤ X = ⊤)
  {F : Type} [Field F] [Finite F] [Algebra (ZMod 2) F]
  {n : ℕ} (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n) (e : K ≃* PSL(3,F))

omit [Finite D] [X.Normal] in
include hmark in
private theorem centralizes_marked_cubic {A : Subgroup D}
    (hAX : A ≤ centralizer (X : Set D)) : ∀ a ∈ A, Commute a (s cubic) := by
  have hxmem : s cubic ∈ X := by
    rw [← hmark]
    exact mem_map_of_mem s (show cubic ∈ alternatingGroup (Fin 3) from by
      change Equiv.Perm.sign cubic = 1
      decide +kernel)
  intro a ha
  exact (hAX ha (s cubic) hxmem).symm

include hB42 hInv hS hf hx hc hs hmark hg hn ho hF e in
/-- The recognized central quotient lifts to an actual odd-dimensional natural
constituent, with its original marking and the numerical half-codimension bound. -/
theorem quadratic_minimal_split_constituent (A : Subgroup D)
    (hA : IsMinimalBestOffender ρ A) (hquad : IsQuadratic ρ A) :
    A ≤ centralizer (X : Set D) ∧
    ∃ (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
      (hAI : A ≤ subspaceStabilizer ρ I),
      Disjoint I (fixedSpace ρ K) ∧
      IsProjectiveNaturalOrDual ho hF
        ((invariantSubspace ρ K I hI.choose).toRepresentation.comp e.symm.toMonoidHom) ∧
      Odd (Module.finrank (ZMod 2) I) ∧
      rank A ≤ 2 * fixedCodim (constituentAction ρ K A I hI.choose hAI)
        (A.subgroupOf (K ⊔ A)) := by
  obtain ⟨hAX, I, hI, hAI, hnat, _, hnum, _⟩ :=
    quadratic_minimal_constituent ρ K A hB42 hInv hS hf X hx hc s hs hmark hg hn ho hF e hA hquad
  have hd := CentralSplitting.disjoint_fixedSpace hn ho hF ρ K e I hI hnat
  have hi := CentralSplitting.naturalOrDual hn ho hF ρ K e I hI hnat
  refine ⟨hAX, I, hI, hAI, hd, hi, ?_, hnum⟩
  have hdim : Module.finrank (ZMod 2) I = 3 * n := naturalOrDual_finrank ho hF _ hi
  rw [hdim]
  exact (by decide : Odd 3).mul ho

include hB42 hInv hS hf hx hc hs hmark hg hn ho hF e in
/-- A quadratic minimal best offender pays its full rank on the cubic pair. -/
theorem quadratic_minimal_rank_bound (A : Subgroup D)
    (hA : IsMinimalBestOffender ρ A) (hquad : IsQuadratic ρ A) :
    rank A ≤ fixedCodim ρ A := by
  obtain ⟨hAX, I, hI, hAI, hd, _, hi, hnum⟩ :=
    quadratic_minimal_split_constituent ρ K hB42 hInv hS hf X hx hc s hs hmark hg hn ho hF e A hA hquad
  exact PairSaturation.rank_le_fixedCodim ρ K A s hs
    (ambient_fixedFree_of_commutator ρ s (by rw [hmark]; exact hg))
    (centralizes_marked_cubic X s hmark hAX) I hI hAI hd hi hnum

include hB42 hInv hS hf hx hc hs hmark hg hn ho hF e in
/-- A faithful binary cubic action with the marked odd PSL₃ component is never
strong FF. Quadratic replacement reduces to the doubled constituent bound. -/
theorem no_strong : ¬ IsStrongFFModule ρ := by
  rintro ⟨B, hB⟩
  obtain ⟨A, _, hA, hquad, hstrong⟩ := hB.exists_quadratic_minimalBestOffender ρ
  exact (not_lt_of_ge (quadratic_minimal_rank_bound ρ K hB42 hInv hS hf X hx hc
    s hs hmark hg hn ho hF e A hA hquad)) hstrong.2

include hB42 hInv hS hf hx hc hs hmark hg hn ho hF e in
/-- For an FF action the full K-moved space is a natural cubic tensor module:
the canonical inverter-fixed multiplicity of the literal W/0 section is natural
or binary dual-natural under the supplied component marking. -/
theorem moved_natural_of_ff (hff : IsFFModule ρ)
    (W : Subrepresentation ρ) (hW : W.toSubmodule = subspaceCommutator ρ ⊤ K) :
    IsProjectiveNaturalOrDual ho hF
      ((sectionMultiplicityAction ρ K.subtype s hs ⊥ W).comp e.symm.toMonoidHom) := by
  obtain ⟨B, hB⟩ := hff
  obtain ⟨A, _, hA, hquad, _⟩ := hB.exists_quadratic_minimalBestOffender ρ
  obtain ⟨hAX, I, hI, hAI, hd, hi, hodd, hnum⟩ :=
    quadratic_minimal_split_constituent ρ K hB42 hInv hS hf X hx hc s hs hmark hg hn ho hF e A hA hquad
  obtain ⟨a, ha⟩ := PairSaturation.offender_multiplicity_coordinates ρ K A s hs
    (ambient_fixedFree_of_commutator ρ s (by rw [hmark]; exact hg))
    (centralizes_marked_cubic X s hmark hAX)
    (component_commutator_of_centralizes_cubic K X hx hc hA.1.1 hAX)
    I hI hAI hd hodd hnum (hA.1.isOffender ρ) W hW
  rcases hi with ⟨f, hf⟩ | ⟨f, hf⟩
  · exact Or.inl ⟨a.trans f, fun g v => by
      change f (a (sectionMultiplicityAction ρ K.subtype s hs ⊥ W (e.symm g) v)) = _
      rw [ha]
      exact hf g (a v)⟩
  · exact Or.inr ⟨a.trans f, fun g v => by
      change f (a (sectionMultiplicityAction ρ K.subtype s hs ⊥ W (e.symm g) v)) = _
      rw [ha]
      exact hf g (a v)⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.CubicFF
