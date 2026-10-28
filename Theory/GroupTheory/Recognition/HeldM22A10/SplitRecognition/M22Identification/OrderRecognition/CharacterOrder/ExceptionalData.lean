module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysisData
public import Theory.Character.Induction
public import Theory.Character.InvolutionRootPairing

/-!+# Interfaces for the exceptional-character order calculation

The five integer combinations below are exactly those on Janko's p.12, with
zero-based indices. Their scalar products and five special columns are fixed
numerical data. `SpecialInductionData` asks for actual irreducible characters
of the actual normalizer of E, and assertions about their actual induction.
It does not construct those characters or assert the order theorem.

The independent pair-count calculation and signed-decomposition argument have
separate interfaces. Proving their inhabitants remains necessary before using
them in ambient order recognition. No ambient order or identification is a field.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Sections 6–7, pp.11–15. The page images, rather than OCR,
determine all entries and signs.
-/

open scoped BigOperators
open Subgroup
noncomputable section
attribute [local instance] Fintype.ofFinite

namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
namespace CharacterOrder
universe u

/-- Coefficients of ψ₁,…,ψ₅ in χ₁,…,χ₁₂ (both indexed from zero). -/
@[expose] public def exceptionalCoefficients : Fin 5 → Fin 12 → ℤ :=
  ![![0, 0, 1, 0, 0, 1, 0, 0, 0, 0, -1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, -1, -1, 0],
    ![1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1],
    ![0, 1, 0, 1, 1, 0, 1, 0, 0, -1, 0, 0],
    ![0, 0, 1, 0, 0, -1, -1, 1, -1, 0, 0, 0]]

/-- The Gram matrix of the five exceptional combinations. -/
@[expose] public def exceptionalGram : Fin 5 → Fin 5 → ℤ :=
  ![![3, 1, 1, 0, 0], ![1, 3, 0, 1, 1], ![1, 0, 4, 1, -1],
    ![0, 1, 1, 5, -1], ![0, 1, -1, -1, 5]]

/-- The integral matrix product giving the Gram matrix. This calculation
does not by itself construct or identify a character table. -/
public theorem exceptionalGram_eq : ∀ i j,
    exceptionalGram i j =
      ∑ r : Fin 12, exceptionalCoefficients i r * exceptionalCoefficients j r := by
  decide +kernel

/-- Source special representatives in order z₁, cz₁, z₂bd, z₄a, z₂d. -/
@[expose] public def specialRepresentative : Fin 5 → TwistedModel :=
  ![CaseII.z 0, CaseII.c * CaseII.z 0, CaseII.z 1 * CaseII.b * CaseII.d,
    CaseII.z 3 * CaseII.a, CaseII.z 1 * CaseII.d]

/-- The five exceptional characters on the five special classes. -/
@[expose] public def exceptionalValues : Fin 5 → Fin 5 → ℤ :=
  ![![16, 4, -2, -4, 0], ![0, 0, 0, -8, 4], ![16, 4, 2, 4, 4],
    ![32, -4, 0, 0, 4], ![0, 0, 4, -8, -4]]

/-- Frobenius reciprocity recovers these five values of an ambient irreducible
from its five integral exceptional multiplicities. -/
@[expose] public def columnValue (c : Fin 5 → ℤ) : Fin 5 → ℤ :=
  ![7 * c 0 - 6 * c 1 + c 2 + 8 * c 3 + 3 * c 4,
    c 0 + c 2 - c 3, -c 0 + c 2 + c 4,
    -c 0 - 2 * c 1 + c 2 - c 4, -c 0 + 2 * c 1 + c 2 - c 4]

variable {G : Type u} [Group G] [Finite G]

/-- The actual inductions to G of the five specified normalizer combinations. -/
@[expose] public def exceptionalInduction (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer)
    (χ : Fin 12 → ClassFunction (normalizer (CaseII.E D k : Set G)))
    (i : Fin 5) : ClassFunction G :=
  inducedClassFunction (normalizer (CaseII.E D k : Set G))
    (∑ r : Fin 12, (exceptionalCoefficients i r : ℂ) • χ r)

/-- Genuine character and induction conclusions whose construction is the
normalizer-character prerequisite. The `columns` clause is the p.12 reciprocity
calculation, not an assumption on ambient character degrees or group order. -/
public structure SpecialInductionData (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) where
  character : Fin 12 → ClassFunction (normalizer (CaseII.E D k : Set G))
  irreducible : ∀ r, IsIrreducibleCharacter (character r)
  injective : Function.Injective character
  principal : character 0 = 1
  degree_zero : ∀ i, exceptionalInduction D k character i 1 = 0
  gram : ∀ i j, scalarProduct G
    (exceptionalInduction D k character i) (exceptionalInduction D k character j) =
      (exceptionalGram i j : ℂ)
  principal_multiplicity : ∀ i, scalarProduct G
    (exceptionalInduction D k character i) 1 = (exceptionalCoefficients i 0 : ℂ)
  values : ∀ i r, exceptionalInduction D k character i
    (CaseII.into D k (specialRepresentative r)) = (exceptionalValues i r : ℂ)
  support : ∀ i g, (∀ r, ¬ IsConj g (CaseII.into D k (specialRepresentative r))) →
    exceptionalInduction D k character i g = 0
  columns : ∀ χ : ClassFunction G, IsIrreducibleCharacter χ →
    ∃ c : Fin 5 → ℤ,
      (∀ i, scalarProduct G (exceptionalInduction D k character i) χ = (c i : ℂ)) ∧
      ∀ r, χ (CaseII.into D k (specialRepresentative r)) = (columnValue c r : ℂ)

/-- An abbreviation for the actual induced functions in the preceding data. -/
@[expose] public def SpecialInductionData.induced {D : LocalData G}
    {k : TwistedModel ≃* D.centralizer} (I : SpecialInductionData D k) :
    Fin 5 → ClassFunction G := exceptionalInduction D k I.character

/-- Right sides of the five Suzuki identities, in source order. Their
identification with actual involution-pair counts is a separate obligation. -/
@[expose] public def pairingConstants : Fin 5 → ℚ := ![31 / 12, -1, 91 / 12, 25 / 6, -5]

/-- The local counting input, stated with actual ambient involution pairs. -/
@[expose] public def HasSuzukiPairings {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
    (I : SpecialInductionData D k) : Prop := ∀ i,
  scalarProduct G (I.induced i) (fun g => (Theory.Character.involutionPairCount g : ℂ)) =
    (pairingConstants i : ℂ)

/-- A family of distinct nonprincipal irreducibles, each with a sign. -/
public structure SignedFamily (G : Type u) [Group G] (n : ℕ) where
  character : Fin n → ClassFunction G
  irreducible : ∀ r, IsIrreducibleCharacter (character r)
  injective : Function.Injective character
  nonprincipal : ∀ r, character r ≠ 1
  sign : Fin n → ℤ
  sign_eq : ∀ r, sign r = 1 ∨ sign r = -1

/-- A signed irreducible as an actual class function. -/
@[expose] public def SignedFamily.term {n : ℕ} (F : SignedFamily G n)
    (r : Fin n) : ClassFunction G := (F.sign r : ℂ) • F.character r

/-- Lemma 11's precise multiplicity conclusion. -/
@[expose] public def HasUnitMultiplicities (ψ : Fin 5 → ClassFunction G) : Prop :=
  ∀ χ : ClassFunction G, IsIrreducibleCharacter χ → ∀ i,
    scalarProduct G (ψ i) χ = 0 ∨ scalarProduct G (ψ i) χ = 1 ∨
      scalarProduct G (ψ i) χ = -1

/-- Both cases of Lemma 12. Indices 0,1,2 are X₁,X₂,X₃; indices 3,4
are Y₁,Y₂; the remaining indices are Z₁ and (in the first case) Z₂. -/
@[expose] public def HasJankoDecomposition (ψ : Fin 5 → ClassFunction G) : Prop :=
  (∃ F : SignedFamily G 7,
    ψ 0 = F.term 0 + F.term 1 + F.term 2 ∧
    ψ 1 = F.term 0 + F.term 3 + F.term 4 ∧
    ψ 2 = 1 + F.term 1 + F.term 5 + F.term 6) ∨
  (∃ F : SignedFamily G 6,
    ψ 0 = F.term 0 + F.term 1 + F.term 2 ∧
    ψ 1 = F.term 0 + F.term 3 + F.term 4 ∧
    ψ 2 = 1 + F.term 0 - F.term 3 + F.term 5)

end CharacterOrder
end Theory.GroupTheory.HeldM22A10.M22Identification
