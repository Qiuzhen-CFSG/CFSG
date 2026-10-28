module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.Contrary.Held
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.Adequate.Replacement

/-!
# The contrary source contradiction from the adequate intrinsic implication

The residual replacement retains all three actual component possibilities.
The new Held branch is excluded from the original source pair, in both
Fitting cases. The other two branches use their actual model conclusions to
construct the ordinary source context and then the characteristic-two input.
Full marked 1.1.5 is discharged using the genuine universal A/B/C theorem.

The complete adequate embedding, component-orbit, two-orbit residual, C.2.7,
C.1.34 and adequate B.5 implications remain explicit earlier-source inputs.
No original Held-excluding embedding theorem is assumed. This deduction does
not discharge those earlier universal implications.
Source: Aschbacher--Smith, 15.4.20, pp.1163--1164.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.Contrary
open FamilySource FamilySource.ModuleStructure EmbeddingReduction CoreElimination
open ComponentElimination.OrdinaryReduction BlockSieve.ExchangedCases.SourceAssembly
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable {T : Sylow 2 G} {M₁ M₂ X Y : Subgroup G}

/-- The ordinary source branch consumes its two actual embedding cases. -/
theorem source_characteristicTwo_of_cases
    (hX : Input κ T M₁ X 2) (pX : Pair T M₁ X) (pY : Pair T M₂ Y)
    (hM₁ : normalizer (X : Set G) = M₁)
    (huniqueX : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M₁)
    (hZcard : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (earlierOneTwo : TwoFactors.Prebranch.Lemma115OneTwo κ G)
    (earlierThree : Chapter15.Section03.Candidates.ComponentStructure.Earlier115Three κ G)
    {i j : Bool} {H U K : Subgroup G}
    (h : PlacedX (geometry pX pY) i j H U)
    (P : Sylow 3 (geometry pX pY).wholeX)
    (hgen : K ⊔ U = H)
    (hclosure : K = normalClosureIn (geometry pX pY).wholeX H)
    (hres : K = (primeToResidual 3 H).map H.subtype)
    (branch : BinaryCase H U K ∨ ExchangedCase H U
      ((P : Subgroup (geometry pX pY).wholeX).map (geometry pX pY).wholeX.subtype) K) :
    generalizedFitting K = pCore 2 K := by
  let d := geometry pX pY
  let s : SourceContext d i j H K U := {
    placed := h
    closure := hclosure
    residual := hres
    generation := hgen.symm
    omega := rfl
    four := hZcard
    local115 := placed_local115 hX.ambient h rfl }
  have hx : d.wholeX = X := pX.quotient.factor_generate hX
  have hm₁ : d.M₁ = M₁ := by change normalizer (d.wholeX : Set G) = M₁; rw [hx,hM₁]
  have ha : TwoFactors.MixedLocal.FactorPairAction d.M₁ d.X := by
    rw [hm₁]
    exact pX.quotient.action
  have hVM : IsElementaryAbelian 2 d.VM₁ := localV_elementary T M₁ hX.sylow_le
    (hX.ambient.evenCharacteristic T M₁ hX.maximal hX.sylow_le)
  have hVM_eq : d.VM₁ = normalClosureIn d.Z d.M₁ := by
    change localV T M₁ = normalClosureIn d.Z d.M₁
    rw [hm₁]
    rfl
  have hu : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      d.wholeX ⊔ (d.T : Subgroup G) ≤ N → N = d.M₁ := by
    rw [hx,hm₁]
    exact huniqueX
  exact ComponentElimination.generalizedFitting_eq_twoCore_of_source hX.ambient
    earlierOneTwo earlierThree s (embeddingAlternatives_of_cases hgen.symm branch) ha
    hVM hVM_eq (pX.module_card i) hu


/-- Full contrary-source exclusion with Held retained by the intrinsic theorem. -/
theorem source_contradiction_of_adequate_embedding
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
    (embedding : Chapter1.XiEmbedding.AdequateLocalEmbeddingTheorem.{u} KnownSimple.IsKnownSimple)
    (orbits : ComponentOrbitTheorem.{u} KnownSimple.IsKnownSimple)
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
    h.adequate_replacement hX.ambient embedding orbits residual P
  have branch : BinaryCase D U K ∨ ExchangedCase D U
      ((P : Subgroup d.wholeX).map d.wholeX.subtype) K := by
    rcases branches with hb | he | hh
    · exact Or.inl hb
    · exact Or.inr he
    · obtain ⟨hK, _, hq, ⟨e⟩⟩ := hh
      exact (source_held_contradiction hX pX pY hM₁ huniqueX hZcard hABC c27
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
