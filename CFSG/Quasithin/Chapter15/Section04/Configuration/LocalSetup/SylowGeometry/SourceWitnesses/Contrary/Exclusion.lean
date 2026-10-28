module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.Contrary
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.Contrary.ResidualReplacement
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.ComponentInputs
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.BinaryBranch.SourceClassification.Recognition.Assembly

/-!
# The characteristic-two contrary branch from the original source pairs

Replace the placed overgroup H by D=KU, with K its actual X-normal closure.
The residual sandwich identifies the same K with the normal closure and
three-prime residual inside D. The original two pairs then construct every
ContraryData and BlockSieve.Input field for this replacement. The binary
module theorem and the exchanged C.2.7/C.1.34 sieve exclude the two actual
embedding outputs, without assuming contrary data or a local classifier.

The genuine universal earlier implications remain explicit. In particular,
this theorem uses the original LocalEmbeddingTheorem. It does not discharge
that theorem or replace the separate adequate intrinsic embedding route,
whose additional Held alternative remains a source-assembly obligation.
Source: Aschbacher–Smith, 15.4.20, printed pp.1163–1164.
-/

@[expose] public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.Contrary
open FamilySource FamilySource.ModuleStructure EmbeddingReduction CoreElimination
open BlockSieve.ExchangedCases.SourceAssembly
universe u

private theorem binary_model_equiv {Q : Type*} [Group Q] {n : ℕ}
    (h : ClassicalGroup.IsPSL Q n 2) :
    Nonempty (Q ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) := by
  obtain ⟨F, _, _, hF, ⟨a⟩⟩ := h
  let : Fintype F := Fintype.ofFinite F
  let b : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  exact ⟨a.trans (Atlas.fieldEquivPSL n b)⟩

/-- The abstract binary model from the embedding theorem has exactly the
concrete automorphism quotient required by the original binary sieve. -/
theorem binaryCase_excluded {G : Type u} [Group G] [Finite G]
    {d : Source.Geometry G} {i j : Bool} {H U K : Subgroup G}
    (h : BlockSieve.Input d i j H U K)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (b5 : TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ProjectiveLine.QuasisimpleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple)
    (branch : BinaryCase H U K) : False := by
  obtain ⟨hK, _, _, _, hm, ⟨a⟩⟩ := branch
  have ha : Nonempty ((H ⧸ pCore 2 H) ≃* MulAut (K ⧸ pCore 2 K)) := by
    change Nonempty (Chapter1.XiQuotient H ≃* MulAut (Chapter1.XiQuotient K))
    rw [← h.generation]
    exact ⟨a⟩
  obtain ⟨a⟩ := ha
  apply BlockSieve.BinaryBranch.SourceClassification.Recognition.not_binaryEmbedding h hH b5
  refine ⟨hK, ?_⟩
  rcases hm with hm | hm
  · obtain ⟨e⟩ := binary_model_equiv hm
    exact ⟨4, Or.inl rfl, ⟨a.trans (MulAut.congr e)⟩⟩
  · obtain ⟨e⟩ := binary_model_equiv hm
    exact ⟨5, Or.inr rfl, ⟨a.trans (MulAut.congr e)⟩⟩

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {M₁ M₂ X Y : Subgroup G}

/-- Construct the actual contrary inputs after residual replacement and
exclude the genuine characteristic-two branch from the original two pairs. -/
theorem source_characteristicTwo_contradiction
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
    (c27 : UniversalC27.{u})
    (c134 : BlockSieve.ExchangedCases.SL3Geometry.SourceCases.UniversalClassification.{u})
    (b5 : TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ProjectiveLine.QuasisimpleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple)
    {i j : Bool} {H U : Subgroup G}
    (h : PlacedX (geometry pX pY) i j H U)
    (hchar : generalizedFitting (normalClosureIn (geometry pX pY).wholeX H) =
      pCore 2 (normalClosureIn (geometry pX pY).wholeX H)) : False := by
  let d := geometry pX pY
  let K := normalClosureIn d.wholeX H
  let D := K ⊔ U
  let P : Sylow 3 d.wholeX := Classical.choice inferInstance
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨hD⟩, branch⟩ :=
    h.embedding_residual_reduction hX.ambient embedding orbits residual P
  have hid := replacement_identifications_of_placed hX.ambient embedding orbits residual h P hD
  have hclosure : K = normalClosureIn d.wholeX D := hid.1
  have hres : K = (primeToResidual 3 D).map D.subtype := hid.2.1
  let c := contraryData hX hY pX pY hWX hWY hM₁ hM₂ huniqueX huniqueY
    hne hZcard hCZ hD rfl hclosure hres hchar
  let s := contraryInput hX pX pY hZcard hD rfl hclosure hres hchar
  rcases branch with hb | he
  · exact binaryCase_excluded s (hD.embedding_input hX.ambient P).1 b5 hb
  · exact exchanged_case_contradiction c27 c134 c s P he

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses.Contrary
