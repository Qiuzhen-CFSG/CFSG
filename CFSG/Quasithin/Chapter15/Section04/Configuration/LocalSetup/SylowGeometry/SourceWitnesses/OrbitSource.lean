module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.OrbitSource
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.AdequateEndgame.FullSource
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.Contrary.Held.FFSource

/-!
# The actual 15.4.19--20 witnesses from source component orbits

The original module inputs construct the contrary overgroup. Its intrinsic
embedding and normal-or-index-two component bound are now proved, retaining
all binary, exchanged and Held cases. This constructs the simultaneous
four-choice Sylow conclusions and every field of the original LocalData;
the corrected full-source endgame then excludes the double pair.

The genuine two-orbit residual, C.2.7 and C.1.34 implications remain explicit.
Source: Aschbacher--Smith 15.4.19--25, printed pp.1164--1165.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.Contrary
open FamilySource FamilySource.ModuleStructure EmbeddingReduction CoreElimination
open ComponentElimination.OrdinaryReduction BlockSieve.ExchangedCases.SourceAssembly
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable {T : Sylow 2 G} {M₁ M₂ X Y : Subgroup G}

theorem source_contradiction_of_adequate_embedding_sourceOrbit
    (hX : Input KnownSimple.IsKnownSimple T M₁ X 2)
    (hY : Input KnownSimple.IsKnownSimple T M₂ Y 2)
    (pX : Pair T M₁ X) (pY : Pair T M₂ Y)
    (hWX : movedModule T M₁ X ≤ ChapterB.baumann (T : Subgroup G))
    (hWY : movedModule T M₂ Y ≤ ChapterB.baumann (T : Subgroup G))
    (hM₁ : normalizer (X : Set G) = M₁) (hM₂ : normalizer (Y : Set G) = M₂)
    (huniqueX : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M₁)
    (huniqueY : ∀ N : Subgroup G, IsMaximalTwoLocal N → Y ⊔ (T : Subgroup G) ≤ N → N = M₂)
    (hne : M₁ ≠ M₂)
    (hZcard : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (hCZ : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (X : Set G) ≠ ⊥)
    (residual : TwoOrbitResidualTheorem.{u} KnownSimple.IsKnownSimple)
    (hABC : ∀ (A : Type u) [Group A] [Finite A],
      ChapterA.Section02.TheoremsABC KnownSimple.IsKnownSimple A)
    (c27 : UniversalC27.{u})
    (c134 : BlockSieve.ExchangedCases.SL3Geometry.SourceCases.UniversalClassification.{u})
    (b5 : TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ProjectiveLine.QuasisimpleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple)
    {i j : Bool} {H U : Subgroup G}
    (h : PlacedX (geometry pX pY) i j H U) : False := by
  let d := geometry pX pY
  let K := normalClosureIn d.wholeX H
  let D := K ⊔ U
  let P : Sylow 3 d.wholeX := Classical.choice inferInstance
  obtain ⟨hD, hclosure, hres, branches⟩ :=
    h.adequate_replacement_sourceOrbit hX.ambient residual P
  have branch : BinaryCase D U K ∨ ExchangedCase D U
      ((P : Subgroup d.wholeX).map d.wholeX.subtype) K := by
    rcases branches with hb | he | hh
    · exact Or.inl hb
    · exact Or.inr he
    · obtain ⟨hK, _, hq, ⟨e⟩⟩ := hh
      exact (source_held_contradiction_from_ff hX pX pY hM₁ huniqueX hZcard
        hD rfl hclosure hres hK.2 hq e).elim
  have hchar := source_characteristicTwo_of_cases hX pX pY hM₁ huniqueX hZcard
    SourceRecognition.Source.earlier115OneTwo (SourceRecognition.Source.earlier115Three hABC)
    hD P rfl hclosure hres branch
  let c := contraryData hX hY pX pY hWX hWY hM₁ hM₂ huniqueX huniqueY
    hne hZcard hCZ hD rfl hclosure hres hchar
  let s := contraryInput hX pX pY hZcard hD rfl hclosure hres hchar
  rcases branch with hb | he
  · exact binaryCase_excluded s (hD.embedding_input hX.ambient P).1 b5 hb
  · exact exchanged_case_contradiction c27 c134 c s P he

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.Contrary

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
open FamilySource FamilySource.ModuleStructure EmbeddingReduction
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M₁ M₂ X Y : Subgroup G}

theorem source_geometry_overgroup_sylow_of_adequate_embedding_sourceOrbit
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
    (residual : TwoOrbitResidualTheorem.{u} KnownSimple.IsKnownSimple)
    (hABC : ∀ (A : Type u) [Group A] [Finite A],
      ChapterA.Section02.TheoremsABC KnownSimple.IsKnownSimple A)
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
    exact Contrary.source_contradiction_of_adequate_embedding_sourceOrbit hX hY pX pY hWX hWY hM₁ hM₂ huniqueX huniqueY
      hne hZcard hCZX residual hABC c27 c134 b5 hp
  · obtain ⟨hp⟩ := hp
    exact Contrary.source_contradiction_of_adequate_embedding_sourceOrbit hY hX pY pX hWY hWX hM₂ hM₁ huniqueY huniqueX
      hne.symm hZcard hCZY residual hABC c27 c134 b5 hp

/-- Every field of LocalData is constructed on the original pair geometry;
the uniform Sylow family is proved by the preceding contradiction. -/
theorem source_geometry_localData_of_adequate_embedding_sourceOrbit
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
    (residual : TwoOrbitResidualTheorem.{u} KnownSimple.IsKnownSimple)
    (hABC : ∀ (A : Type u) [Group A] [Finite A],
      ChapterA.Section02.TheoremsABC KnownSimple.IsKnownSimple A)
    (c27 : CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.UniversalC27.{u})
    (c134 : CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.UniversalClassification.{u})
    (b5 : TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ProjectiveLine.QuasisimpleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple) :
    Nonempty (Source.LocalData (geometry pX pY)) :=
  source_geometry_localData_from_input hX hY pX pY hM₁ hM₂ huniqueX huniqueY hne
    hZcard hCZX (source_geometry_overgroup_sylow_of_adequate_embedding_sourceOrbit hX hY pX pY hM₁ hM₂ hS₁ hS₂ huniqueX huniqueY hne hZcard hCZX hCZY
      residual hABC c27 c134 b5)

/-- Source19--20 and all subsequent local-identification inputs are
constructed simultaneously, retaining the actual J, Z and V(M) subgroups. -/
theorem source_lemma_15_4_19_20_of_adequate_embedding_sourceOrbit
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
    (residual : TwoOrbitResidualTheorem.{u} KnownSimple.IsKnownSimple)
    (hABC : ∀ (A : Type u) [Group A] [Finite A],
      ChapterA.Section02.TheoremsABC KnownSimple.IsKnownSimple A)
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
  · exact source_geometry_overgroup_sylow_of_adequate_embedding_sourceOrbit hX hY pX pY hM₁ hM₂ hS₁ hS₂ huniqueX huniqueY hne hZcard hCZX hCZY
      residual hABC c27 c134 b5
  · exact source_geometry_localData_of_adequate_embedding_sourceOrbit hX hY pX pY hM₁ hM₂ hS₁ hS₂ huniqueX huniqueY hne hZcard hCZX hCZY
      residual hABC c27 c134 b5

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
open FamilySource FamilySource.ModuleStructure EmbeddingReduction
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M₁ M₂ X Y : Subgroup G}

theorem source_pair_contradiction_of_adequate_embedding_full_source_sourceOrbit
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
    (residual : TwoOrbitResidualTheorem.{u} KnownSimple.IsKnownSimple)
    (hABC : ∀ (A : Type u) [Group A] [Finite A],
      ChapterA.Section02.TheoremsABC KnownSimple.IsKnownSimple A)
    (c27 : CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.UniversalC27.{u})
    (c134 : CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.UniversalClassification.{u})
    (sourceB : TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ProjectiveLine.AdequateCompleteClassificationInput.{u,u}
      KnownSimple.IsKnownSimple)
    (sourceF : Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SourceClassificationInput.{u}
      KnownSimple.IsKnownSimple) :
    False := by
  obtain ⟨hdata⟩ := source_geometry_localData_of_adequate_embedding_sourceOrbit hX hY pX pY hM₁ hM₂
    hS₁ hS₂ huniqueX huniqueY hne hZcard hCZX hCZY residual hABC
    c27 c134 sourceB.quasisimple
  exact SourceRecognition.TwoCore.FullSource.source_endgame hdata hX.ambient sourceF sourceB
    (SourceRecognition.Source.earlier115 hX.ambient hABC) rfl

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
