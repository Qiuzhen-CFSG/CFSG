module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.AlphaGeometry.FromInput
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.Placed
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.Contrary.ComponentBranch

/-!
# Uniform source Sylow control and simultaneous LocalData

A failed Sylow conclusion gives a maximal contrary choice in one of the two
original orientations. All action and marked-quotient witnesses are constructed
from the source Input. The ordinary and characteristic-two reductions exclude
that choice. Thus T₀ is Sylow in every H-overgroup of each of the four amalgams.
The already proved source19 and post-Sylow transfer construct all LocalData.

The complete earlier universal implications remain explicit. In particular the
original LocalEmbeddingTheorem is still unresolved; this conditional theorem
does not discharge the separate source-adequate Held branch. No source module,
placed configuration, generalized-Fitting equality or LocalData is assumed.
Source: Aschbacher--Smith, 15.4.19--20, printed pp.1163--1164.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
open FamilySource FamilySource.ModuleStructure EmbeddingReduction
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M₁ M₂ X Y : Subgroup G}

/-- The full four-choice overgroup-Sylow conclusion from raw source data and
the exact earlier universal implications. -/
theorem source_geometry_overgroup_sylow_of_original_embedding
    (hX : Input KnownSimple.IsKnownSimple T M₁ X 2)
    (hY : Input KnownSimple.IsKnownSimple T M₂ Y 2)
    (pX : Pair T M₁ X) (pY : Pair T M₂ Y)
    (hM₁ : normalizer (X : Set G) = M₁) (hM₂ : normalizer (Y : Set G) = M₂)
    (hS₁ : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M₁)
    (hS₂ : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M₂)
    (huniqueX : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M₁)
    (huniqueY : ∀ N : Subgroup G, IsMaximalTwoLocal N → Y ⊔ (T : Subgroup G) ≤ N → N = M₂)
    (hne : M₁ ≠ M₂)
    (hZcard : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hCZX : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (X : Set G) ≠ ⊥)
    (hCZY : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (Y : Set G) ≠ ⊥)
    (embedding : LocalEmbeddingTheorem.{u} KnownSimple.IsKnownSimple)
    (orbits : ComponentOrbitTheorem.{u} KnownSimple.IsKnownSimple)
    (residual : TwoOrbitResidualTheorem.{u} KnownSimple.IsKnownSimple)
    (earlierOneTwo : TwoFactors.Prebranch.Lemma115OneTwo KnownSimple.IsKnownSimple G)
    (earlierThree : Chapter15.Section03.Candidates.ComponentStructure.Earlier115Three KnownSimple.IsKnownSimple G)
    (c27 : CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.UniversalC27.{u})
    (c134 : CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.UniversalClassification.{u})
    (b5 : TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ProjectiveLine.QuasisimpleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple) :
    ∀ i j, ∀ H ∈ Chapter1.HOver G ((geometry pX pY).I i j : Set G),
      ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = (geometry pX pY).T₀ := by
  intro i j H hH
  by_contra hfail
  obtain ⟨a,b,A,U,hplaced⟩ := exists_source_placed_counterexample hX hY pX pY
    hM₁ hM₂ hS₁ hS₂ huniqueX huniqueY hne ⟨i,j,H,hH,hfail⟩
  have hWX := (MarkedProduct.source_baumann_module hX).2.2.1
  have hWY := (MarkedProduct.source_baumann_module hY).2.2.1
  rcases hplaced with hp | hp
  · obtain ⟨hp⟩ := hp
    exact Contrary.source_contradiction hX hY pX pY hWX hWY hM₁ hM₂ huniqueX huniqueY
      hne hZcard hCZX embedding orbits residual earlierOneTwo earlierThree c27 c134 b5 hp
  · obtain ⟨hp⟩ := hp
    exact Contrary.source_contradiction hY hX pY pX hWY hWX hM₂ hM₁ huniqueY huniqueX
      hne.symm hZcard hCZY embedding orbits residual earlierOneTwo earlierThree c27 c134 b5 hp

/-- Every field of LocalData is constructed on the original pair geometry;
the uniform Sylow family is proved by the preceding contradiction. -/
theorem source_geometry_localData_of_original_embedding
    (hX : Input KnownSimple.IsKnownSimple T M₁ X 2)
    (hY : Input KnownSimple.IsKnownSimple T M₂ Y 2)
    (pX : Pair T M₁ X) (pY : Pair T M₂ Y)
    (hM₁ : normalizer (X : Set G) = M₁) (hM₂ : normalizer (Y : Set G) = M₂)
    (hS₁ : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M₁)
    (hS₂ : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M₂)
    (huniqueX : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M₁)
    (huniqueY : ∀ N : Subgroup G, IsMaximalTwoLocal N → Y ⊔ (T : Subgroup G) ≤ N → N = M₂)
    (hne : M₁ ≠ M₂)
    (hZcard : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hCZX : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (X : Set G) ≠ ⊥)
    (hCZY : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (Y : Set G) ≠ ⊥)
    (embedding : LocalEmbeddingTheorem.{u} KnownSimple.IsKnownSimple)
    (orbits : ComponentOrbitTheorem.{u} KnownSimple.IsKnownSimple)
    (residual : TwoOrbitResidualTheorem.{u} KnownSimple.IsKnownSimple)
    (earlierOneTwo : TwoFactors.Prebranch.Lemma115OneTwo KnownSimple.IsKnownSimple G)
    (earlierThree : Chapter15.Section03.Candidates.ComponentStructure.Earlier115Three KnownSimple.IsKnownSimple G)
    (c27 : CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.UniversalC27.{u})
    (c134 : CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.UniversalClassification.{u})
    (b5 : TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ProjectiveLine.QuasisimpleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple) :
    Nonempty (Source.LocalData (geometry pX pY)) :=
  source_geometry_localData_from_input hX hY pX pY hM₁ hM₂ huniqueX huniqueY hne
    hZcard hCZX (source_geometry_overgroup_sylow_of_original_embedding hX hY pX pY hM₁ hM₂ hS₁ hS₂ huniqueX huniqueY hne hZcard hCZX hCZY
      embedding orbits residual earlierOneTwo earlierThree c27 c134 b5)

/-- Source19--20 and all subsequent local-identification inputs are
constructed simultaneously, retaining the actual J, Z and V(M) subgroups. -/
theorem source_lemma_15_4_19_20_of_original_embedding
    (hX : Input KnownSimple.IsKnownSimple T M₁ X 2)
    (hY : Input KnownSimple.IsKnownSimple T M₂ Y 2)
    (hM₁ : normalizer (X : Set G) = M₁) (hM₂ : normalizer (Y : Set G) = M₂)
    (hS₁ : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M₁)
    (hS₂ : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M₂)
    (huniqueX : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M₁)
    (huniqueY : ∀ N : Subgroup G, IsMaximalTwoLocal N → Y ⊔ (T : Subgroup G) ≤ N → N = M₂)
    (hne : M₁ ≠ M₂)
    (hZcard : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hCZX : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (X : Set G) ≠ ⊥)
    (hCZY : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (Y : Set G) ≠ ⊥)
    (embedding : LocalEmbeddingTheorem.{u} KnownSimple.IsKnownSimple)
    (orbits : ComponentOrbitTheorem.{u} KnownSimple.IsKnownSimple)
    (residual : TwoOrbitResidualTheorem.{u} KnownSimple.IsKnownSimple)
    (earlierOneTwo : TwoFactors.Prebranch.Lemma115OneTwo KnownSimple.IsKnownSimple G)
    (earlierThree : Chapter15.Section03.Candidates.ComponentStructure.Earlier115Three KnownSimple.IsKnownSimple G)
    (c27 : CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.UniversalC27.{u})
    (c134 : CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.UniversalClassification.{u})
    (b5 : TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ProjectiveLine.QuasisimpleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple) :
    ∃ d : Source.Geometry G,
      d.T = T ∧ d.wholeX = X ∧ d.wholeY = Y ∧ d.M₁ = M₁ ∧ d.M₂ = M₂ ∧
      d.J = ChapterB.thompsonJ (T : Subgroup G) 0 ∧
      d.Z = Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ∧
      d.VM₁ = localV T M₁ ∧ d.VM₂ = localV T M₂ ∧ Conclusions d ∧
      (∀ i j, ∀ H ∈ Chapter1.HOver G (d.I i j : Set G),
        ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = d.T₀) ∧
      Nonempty (Source.LocalData d) := by
  obtain ⟨pX⟩ := exists_pair hX
  obtain ⟨pY⟩ := exists_pair hY
  let d := geometry pX pY
  have hx : d.wholeX = X := pX.quotient.factor_generate hX
  have hy : d.wholeY = Y := pY.quotient.factor_generate hY
  refine ⟨d,rfl,hx,hy,?_,?_,rfl,rfl,rfl,rfl,?_,?_,?_⟩
  · change normalizer (d.wholeX : Set G) = M₁
    rw [hx,hM₁]
  · change normalizer (d.wholeY : Set G) = M₂
    rw [hy,hM₂]
  · exact source_geometry_conclusions_from_input hX hY pX pY hM₁ hM₂
      huniqueX huniqueY hne hZcard hCZX
  · exact source_geometry_overgroup_sylow_of_original_embedding hX hY pX pY hM₁ hM₂ hS₁ hS₂ huniqueX huniqueY hne hZcard hCZX hCZY
      embedding orbits residual earlierOneTwo earlierThree c27 c134 b5
  · exact source_geometry_localData_of_original_embedding hX hY pX pY hM₁ hM₂ hS₁ hS₂ huniqueX huniqueY hne hZcard hCZX hCZY
      embedding orbits residual earlierOneTwo earlierThree c27 c134 b5

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
