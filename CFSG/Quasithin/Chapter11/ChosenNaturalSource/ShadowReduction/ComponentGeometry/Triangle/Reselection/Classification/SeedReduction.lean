module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification.OrbitFF
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesDefs

/-!
# Returning the FF orbit to the original chosen seed

The literal 3.2.5 alternatives yield seed invariance unless the marked
doubled branch occurs. Equality of subgroup images gives equality of the
original subspaces, so full-normalizer FF transfers without changing any
linear operators. The field-four row comparison excludes the doubled
branch outright for G₂(4); for Sp₄(4) it identifies the exact remaining
symplectic constituent, retaining the original nonisomorphic pair.

Source: Aschbacher--Smith 3.2.5 and 11.0.2, printed pp.580 and 759--760.
The original normalized 7.0.1 and 3.2.5 implications remain with
`qt-d-1222-normalized-nonff` and `qt-baumann-fsu`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification
open Chapter12.Section02 ChapterB.QuasisimpleSource LocalGeometry.Components
private theorem normalizerFF_of_subspace_eq {H W : Type*} [Group H]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (K : Subgroup H)
    {P Q : Submodule (ZMod 2) W} (he : P = Q)
    (hff : IsFFModule (normalizerRepresentation
      ((subspaceImageRepresentation ρ P).comp (restrictedSubgroup ρ P K).subtype))) :
    IsFFModule (normalizerRepresentation
      ((subspaceImageRepresentation ρ Q).comp (restrictedSubgroup ρ Q K).subtype)) := by
  cases he
  exact hff

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L I U : Subgroup G}

/-- The unresolved doubled case has exactly the field-four symplectic
constituent, on its original component action. -/
theorem doubled_symplectic (D : ChosenModule T I U)
    (ho : TriangleOrientation L I) (hd : D.MarkedDoubled) :
    Nat.card (I ⧸ pCore 2 I) = 979200 ∧
      ∃ F : BinaryField, F.degree = 2 ∧ Nonempty
        (ActionEquiv D.seedComponentAction (binarySymplectic F)) := by
  have he := Nat.card_congr (quotientComponentEquiv D (orientation_simple ho)).toEquiv
  obtain ⟨hc, F, hF, hm⟩ := symplectic_of_constituent D.seedComponentAction
    (he ▸ orientation_order ho) hd.2.1
  exact ⟨he.trans hc, F, hF, hm⟩

/-- The G₂ orientation cannot be any of the doubled alternatives of 3.2.5. -/
theorem g2_not_doubled (D : ChosenModule T I U)
    (ho : TriangleOrientation L I)
    (hmodel : ClassificationModels.IsG2At (I ⧸ pCore 2 I) 4) :
    ¬ D.MarkedDoubled := by
  intro hd
  have hc := (doubled_symplectic D ho hd).1
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  let := hF
  let := hfin
  rw [Nat.card_congr e.toEquiv, Atlas.G2.card_Model, hcard] at hc
  norm_num at hc

omit [Finite G] in
/-- Eliminating the one remaining marked alternative fixes the original seed. -/
theorem orbit_eq_seed_of_source325 (D : ChosenModule T I U)
    (h325 : D.Source325Alternatives) (hd : ¬ D.MarkedDoubled) :
    D.sourceOrbit = U := by
  rw [D.sourceOrbit_eq]
  rcases h325 with ⟨he, _⟩ | ⟨he, _, _⟩ | he
  · exact he
  · exact he
  · exact (hd he).elim

omit [Finite G] in
/-- Equality of the literal subgroup images transfers the full normalizer
FF condition to the same seed representation. -/
theorem seed_ff_of_orbit_eq (D : ChosenModule T I U)
    (he : D.sourceOrbit = U) (hff : IsFFModule D.sourceOrbitNormalizerRepresentation) :
    IsFFModule (normalizerRepresentation D.chosenAction) := by
  have hspace : D.orbitSpace = D.space := ReducedNormal.subspaceImage_injective
    (I ⊔ (T : Subgroup G)) (he.trans D.image_eq.symm)
  apply (fullNormalizer_ff_iff D).mpr
  exact normalizerFF_of_subspace_eq (reducedRepresentation (I ⊔ (T : Subgroup G)))
    (I.subgroupOf (I ⊔ (T : Subgroup G))) hspace hff

/-- Conditional source assembly: after the marked doubled branch is
excluded, the earlier conclusions supply both missing seed properties. -/
theorem seed_invariant_ff_of_sources (D : ChosenModule T I U)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T I)
    (ho : TriangleOrientation L I)
    (h701 : Chapter7.NormalizedSource.Alternatives G
      D.orbitRepresentation D.orbitComponent)
    (h325 : D.Source325Alternatives) (hd : ¬ D.MarkedDoubled) :
    (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      IsFFModule (normalizerRepresentation D.chosenAction) := by
  have he := orbit_eq_seed_of_source325 D h325 hd
  refine ⟨?_, seed_ff_of_orbit_eq D he (orbit_ff_of_source701 D h ho h701)⟩
  rw [← he, D.sourceOrbit_eq]
  exact le_normalizer_componentOrbit _ _

/-- In the G₂ orientation, the two preceding source conclusions alone
supply invariance and FF on the original chosen seed. -/
theorem g2_seed_invariant_ff_of_sources (D : ChosenModule T I U)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T I)
    (ho : TriangleOrientation L I)
    (hmodel : ClassificationModels.IsG2At (I ⧸ pCore 2 I) 4)
    (h701 : Chapter7.NormalizedSource.Alternatives G
      D.orbitRepresentation D.orbitComponent)
    (h325 : D.Source325Alternatives) :
    (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      IsFFModule (normalizerRepresentation D.chosenAction) :=
  seed_invariant_ff_of_sources D h ho h701 h325 (g2_not_doubled D ho hmodel)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification
