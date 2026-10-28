module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.Contrary.Exclusion
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.Contrary.EmbeddingAlternatives
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.PostSylowInputs
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination

/-!
# Removing the characteristic-two branch assumption

The actual core-normalizer Sylow subgroup of the placed contrary group
constructs every local 1.1.5 input. After the residual replacement, the
complete original embedding outputs give the component-elimination input.
The source component theorem then proves F*(K)=O₂(K) for the unchanged
normal closure K. The previously assembled characteristic-two contradiction
therefore applies without a branch flag or an assumed ContraryData record.

All earlier classification implications remain explicit, including the
original local embedding theorem. This does not eliminate the Held case
of the separate adequate intrinsic embedding route.
Source: Aschbacher–Smith, 15.4.17 and 15.4.20, pp.1162–1164.
-/

@[expose] public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.Contrary
open FamilySource FamilySource.ModuleStructure EmbeddingReduction CoreElimination
open ComponentElimination.OrdinaryReduction BlockSieve.ExchangedCases.SourceAssembly
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- The placed core-normalizer Sylow gives every actual local 1.1.5 input. -/
theorem placed_local115 (hG : IsSimpleQTKE κ G)
    {d : Source.Geometry G} {i j : Bool} {H U : Subgroup G}
    (h : PlacedX d i j H U)
    (hZ : d.Z = omegaOneCenterAmbient (d.T : Subgroup G)) :
    ∀ z ∈ d.Z, z ≠ 1 → ∃ (P : Sylow 2 H) (M : Subgroup G),
      Chapter1.Lemma115Hypotheses H P M z := by
  obtain ⟨S,hS⟩ := h.core_sylow
  obtain ⟨P,_,hlocal,_⟩ := postSylow_local_inputs hG d.T h.overgroup.1 h.upper.le
    (h.sylow_image ▸ map_subtype_le (h.sylow : Subgroup H)) S hS
  intro z hz hzne
  obtain ⟨M,hM⟩ := hlocal z (hZ ▸ hz) hzne
  exact ⟨P,M,hM⟩

variable {T : Sylow 2 G} {M₁ M₂ X Y : Subgroup G}

/-- Component elimination proves characteristic two for the original normal
closure, after constructing its exact reduced source context. -/
theorem source_residual_characteristicTwo
    (hX : Input κ T M₁ X 2) (pX : Pair T M₁ X) (pY : Pair T M₂ Y)
    (hM₁ : normalizer (X : Set G) = M₁)
    (huniqueX : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M₁)
    (hZcard : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4)
    (embedding : LocalEmbeddingTheorem.{u} κ)
    (orbits : ComponentOrbitTheorem.{u} κ)
    (residual : TwoOrbitResidualTheorem.{u} κ)
    (earlierOneTwo : TwoFactors.Prebranch.Lemma115OneTwo κ G)
    (earlierThree : Chapter15.Section03.Candidates.ComponentStructure.Earlier115Three κ G)
    {i j : Bool} {H U : Subgroup G}
    (h : PlacedX (geometry pX pY) i j H U) :
    generalizedFitting (normalClosureIn (geometry pX pY).wholeX H) =
      pCore 2 (normalClosureIn (geometry pX pY).wholeX H) := by
  let d := geometry pX pY
  let K := normalClosureIn d.wholeX H
  let D := K ⊔ U
  let P : Sylow 3 d.wholeX := Classical.choice inferInstance
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨hD⟩, branch⟩ :=
    h.embedding_residual_reduction hX.ambient embedding orbits residual P
  have hid := replacement_identifications_of_placed hX.ambient embedding orbits residual h P hD
  have hclosure : K = normalClosureIn d.wholeX D := hid.1
  have hres : K = (primeToResidual 3 D).map D.subtype := hid.2.1
  let s : SourceContext d i j D K U := {
    placed := hD
    closure := hclosure
    residual := hres
    generation := rfl
    omega := rfl
    four := hZcard
    local115 := placed_local115 hX.ambient hD rfl }
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
    earlierOneTwo earlierThree s (embeddingAlternatives_of_cases rfl branch) ha
    hVM hVM_eq (pX.module_card i) hu

/-- The complete contrary-source contradiction, without assuming either
Fitting branch or any of the later endgame records. -/
theorem source_contradiction
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
    (embedding : LocalEmbeddingTheorem.{u} KnownSimple.IsKnownSimple)
    (orbits : ComponentOrbitTheorem.{u} KnownSimple.IsKnownSimple)
    (residual : TwoOrbitResidualTheorem.{u} KnownSimple.IsKnownSimple)
    (earlierOneTwo : TwoFactors.Prebranch.Lemma115OneTwo KnownSimple.IsKnownSimple G)
    (earlierThree : Chapter15.Section03.Candidates.ComponentStructure.Earlier115Three KnownSimple.IsKnownSimple G)
    (c27 : UniversalC27.{u})
    (c134 : BlockSieve.ExchangedCases.SL3Geometry.SourceCases.UniversalClassification.{u})
    (b5 : TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ProjectiveLine.QuasisimpleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple)
    {i j : Bool} {H U : Subgroup G}
    (h : PlacedX (geometry pX pY) i j H U) : False := by
  exact source_characteristicTwo_contradiction hX hY pX pY hWX hWY hM₁ hM₂
    huniqueX huniqueY hne hZcard hCZ embedding orbits residual c27 c134 b5 h
    (source_residual_characteristicTwo hX pX pY hM₁ huniqueX hZcard
      embedding orbits residual earlierOneTwo earlierThree h)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.Contrary
