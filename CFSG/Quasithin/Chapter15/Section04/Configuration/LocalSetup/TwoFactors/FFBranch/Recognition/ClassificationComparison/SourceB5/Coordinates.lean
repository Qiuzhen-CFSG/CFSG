module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ExhaustiveSource

/-!
# Literal coordinate transport from the proved B.5 source

The historical Chapter 15 interface and the lower B.5 source use separately
declared records for the same fields, actions and moved sections. These maps
copy the fields without changing the original carrier, action, submodule,
quotient map or intertwiner. Both triple-six interfaces use the corrected
projective-line convention: a two-dimensional vector subspace over F₄.

Source: Aschbacher--Smith B.4.2(8), B.5.1--6 and K.1.3.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.SourceB5
namespace Low
export ChapterB.QuasisimpleSource (BinaryField ActionEquiv MarkedActionEquiv MovedSection
  FourDimensionalSource SylowFixedCentralizer)
end Low
universe u v w z

def field (F : Low.BinaryField) : BinaryField where
  Carrier := F.Carrier
  degree := F.degree
  degree_pos := F.degree_pos
  card_eq := F.card_eq

def action {D : Type u} {E : Type v} [Group D] [Group E]
    {V : Type w} {W : Type z} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D V} {σ : Representation (ZMod 2) E W}
    (e : Low.ActionEquiv ρ σ) : ActionEquiv ρ σ :=
  ⟨e.groupEquiv,e.linearEquiv,e.intertwines⟩

def actionBack {D : Type u} {E : Type v} [Group D] [Group E]
    {V : Type w} {W : Type z} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D V} {σ : Representation (ZMod 2) E W}
    (e : ActionEquiv ρ σ) : Low.ActionEquiv ρ σ :=
  ⟨e.groupEquiv,e.linearEquiv,e.intertwines⟩

variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V}

def marked {H L : Subgroup D} {E : Type w} [Group E]
    {W : Type z} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) E W} {M : Subgroup E}
    (e : Low.MarkedActionEquiv ρ H L σ M) : MarkedActionEquiv ρ H L σ M where
  action := action e.action
  contained := e.contained
  subgroupEquiv := e.subgroupEquiv
  compatible := e.compatible

def movedSection {L : Subgroup D} (s : Low.MovedSection ρ L) : MovedSection ρ L :=
  ⟨s.space,s.space_eq,s.central,s.central_eq⟩

def four (s : Low.FourDimensionalSource ρ) : FourDimensionalSource ρ where
  dimension := s.dimension
  indecomposable := s.indecomposable
  space := s.space
  space_eq := s.space_eq
  natural := action s.natural
  offenders := s.offenders
  ratio := s.ratio
  involutions := s.involutions

def sylowFixed [Finite D] {L : Subgroup D} {d : ℕ} {T : Sylow 2 D}
    (s : Low.SylowFixedCentralizer ρ L d T) : SylowFixedCentralizer ρ L d T :=
  ⟨s.extraspecial,s.core_order,s.quotientEquiv,s.no_offenders⟩

theorem nonsplit (h : ChapterB.QuasisimpleSource.NonsplitNatural ρ) : NonsplitNatural ρ := by
  cases h with
  | linearTwo F h => obtain ⟨e⟩ := h; exact .linearTwo (field F) ⟨action e⟩
  | symplectic F h => obtain ⟨e⟩ := h; exact .symplectic (field F) ⟨action e⟩
  | g2 F h => obtain ⟨e⟩ := h; exact .g2 (field F) ⟨action e⟩
  | alternatingSix h => obtain ⟨e⟩ := h; exact .alternatingSix ⟨action e⟩
  | alternatingEight h => obtain ⟨e⟩ := h; exact .alternatingEight ⟨action e⟩
  | derivedG2 h => obtain ⟨e⟩ := h; exact .derivedG2 ⟨action e⟩
  | linearThree h => obtain ⟨e⟩ := h; exact .linearThree ⟨action e⟩

theorem supplement (h : ChapterB.QuasisimpleSource.SupplementNatural ρ) : SupplementNatural ρ := by
  cases h with
  | symplectic F h => obtain ⟨e⟩ := h; exact .symplectic (field F) ⟨action e⟩
  | alternatingSix h => obtain ⟨e⟩ := h; exact .alternatingSix ⟨action e⟩
  | alternatingEight h => obtain ⟨e⟩ := h; exact .alternatingEight ⟨action e⟩
  | linearThree h => obtain ⟨e⟩ := h; exact .linearThree ⟨action e⟩

def tripleSix {L : Subgroup D}
    (s : ChapterB.SourceInduction.ProjectiveLine.TripleSixAction ρ L) :
    ProjectiveLine.TripleSixAction ρ L where
  centerEquiv := s.centerEquiv
  quotientEquiv := s.quotientEquiv
  dimension := s.dimension
  coordinates := s.coordinates
  scalar_linear := s.scalar_linear
  offenders := s.offenders

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.SourceB5
