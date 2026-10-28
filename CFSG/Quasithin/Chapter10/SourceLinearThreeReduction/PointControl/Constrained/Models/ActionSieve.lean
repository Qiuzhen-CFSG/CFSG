module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.Containing

/-!
# The literal containing-action sieve

The proper full-Sylow local component eliminates the small endpoints of
B.5.1 and forces fields larger than two in both SL₃ rows. The surviving
alternatives retain the original moved space, its central quotient, and
every action marking. In particular the exterior-five and exceptional A₇
rows retain their irreducibility and dimensions. The remaining binary
natural–dual and repeated rows are not promoted to irreducible actions.

Models.RankTwoReduction applies this sieve to the literal reduced orbit
and removes its four rank-two actions.
Source: Aschbacher–Smith B.5.1 and 10.2.9, printed pp.99–103,751–752.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open ChapterB.QuasisimpleSource ChapterB.SourceInduction.ProjectiveLine
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings

/-- The four rank-two containing actions, with the literal quotient or moved-space marking. -/
inductive RankTwoAction {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) Q V} {A : Subgroup Q} (s : MovedSection ρ A) : Prop
  | linearThree (F : BinaryField) (large : 1 < F.degree)
      (action : ActionEquiv (s.action.comp A.subtype) (linearNatural F 3))
  | doubleThree (F : BinaryField) (large : 1 < F.degree)
      (action : ActionEquiv (s.space.toRepresentation.comp A.subtype)
        (repeated (linearNatural F 3) 2))
  | symplectic (F : BinaryField) (large : 1 < F.degree)
      (action : ActionEquiv (s.action.comp A.subtype) (binarySymplectic F))
  | g2 (F : BinaryField) (large : 1 < F.degree)
      (action : ActionEquiv (s.action.comp A.subtype) (binaryG2 F))

/-- The remaining actual A₇ and binary-linear actions; no irreducible or fixed layer is discarded. -/
inductive BinaryOrSevenAction {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) Q V} {A : Subgroup Q} (s : MovedSection ρ A) : Prop
  | sevenFour (faithful : Function.Injective s.action)
      (irreducible : IsIrreducible (s.action.comp A.subtype))
      (actor : A ≃* alternatingGroup (Fin 7))
      (dimension : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4)
  | sevenDeleted (faithful : Function.Injective s.action)
      (irreducible : IsIrreducible (s.action.comp A.subtype))
      (action : MarkedActionEquiv s.action (offenderSubgroup s.action) A
        (BinaryPermutation.naturalRepresentation (Fin 7)) (alternatingGroup (Fin 7)))
  | linear (d : ℕ) (degree : d = 4 ∨ d = 5)
      (faithful : Function.Injective s.action) (irreducible : IsIrreducible (s.action.comp A.subtype))
      (action : ActionEquiv (s.action.comp A.subtype) (linearNatural BinaryField.two d))
  | orthogonalSix (faithful : Function.Injective s.action)
      (irreducible : IsIrreducible (s.action.comp A.subtype))
      (action : ActionEquiv (s.action.comp A.subtype) (alternatingNatural 8))
  | symmetricEight (faithful : Function.Injective s.action)
      (irreducible : IsIrreducible (s.action.comp A.subtype))
      (action : MarkedActionEquiv s.action (offenderSubgroup s.action) A
        (BinaryPermutation.naturalRepresentation (Fin 8)) (alternatingGroup (Fin 8)))
  | exteriorFive (faithful : Function.Injective s.action)
      (irreducible : IsIrreducible (s.action.comp A.subtype))
      (actor : A ≃* SL(5,ZMod 2))
      (dimension : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 10)
  | naturalDual (d : ℕ) (degree : d = 4 ∨ d = 5)
      (action : IsNaturalPlusDual (s.space.toRepresentation.comp A.subtype) d)
  | repeatedNatural (d r : ℕ) (degree : d = 4 ∨ d = 5) (positive : 0 < r) (bound : r ≤ d-1)
      (action : IsRepeatedLinearNatural (s.space.toRepresentation.comp A.subtype) BinaryField.two d r)

private theorem proper_local_not_solvable_overgroups
    {A : Type*} [Group A] [Finite A] [IsQuasisimple A]
    (S : Sylow 2 A) (B : Subgroup A) (hB : B ∈ localCComponents S)
    (hp : B ≠ ⊤) (hs : SolvableSylowOvergroups A) : False := by
  have ht : (⊤ : Subgroup A).IsCComponent :=
    (show IsComponent A ⊤ from ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  exact hp (eq_of_solvable_sylow_overgroups S hB ht le_top
    (SolvableSylowOvergroups.of_equiv topEquiv hs))

private theorem containing_three_degree
    {A : Type*} [Group A] [Finite A] [IsQuasisimple A]
    (S : Sylow 2 A) (B : Subgroup A) (hB : B ∈ localCComponents S)
    (hp : B ≠ ⊤) (F : BinaryField) (e : A ≃* SL(3,F.Carrier)) : 1 < F.degree := by
  by_contra hn
  have hn1 : F.degree = 1 := by have := F.degree_pos; omega
  have hc : Nat.card F.Carrier = 2 := by rw [F.card_eq,hn1]; norm_num
  exact proper_local_not_solvable_overgroups S B hB hp
    (SolvableSylowOvergroups.of_equiv e
      (Matrix.PSL3Two.solvableSylowOvergroups_specialLinear_of_card_two hc))

/-- The full-Sylow local sieve retains the exact module markings in B.5.1. -/
theorem containing_action_of_source_case
    {Q V : Type*} [Group Q] [Finite Q] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Q V) (A : Subgroup Q) [IsQuasisimple A]
    (s : MovedSection ρ A) (hc : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ A s)
    (S : Sylow 2 A) (B : Subgroup A) (hB : B ∈ localCComponents S) (hp : B ≠ ⊤) :
    RankTwoAction s ∨ BinaryOrSevenAction s := by
  cases hc with
  | irreducible _ hf hi source _ =>
    cases source with
    | linearTwo F _ a _ _ =>
      exact (proper_local_not_solvable_overgroups S B hB hp
        (SolvableSylowOvergroups.of_equiv a.groupEquiv
          Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup)).elim
    | linearThree F _ a _ =>
      exact Or.inl (.linearThree F (containing_three_degree S B hB hp F a.groupEquiv) a)
    | symplectic F hn _ a _ => exact Or.inl (.symplectic F hn a)
    | symplecticTwo a _ =>
      exact (FiveLocalFF.AlternatingSmall.not_proper_symplectic_two_derived S B hB hp
        a.subgroupEquiv).elim
    | g2 F hn _ a _ _ => exact Or.inl (.g2 F hn a)
    | g2Two a _ _ =>
      exact (proper_local_not_solvable_overgroups S B hB hp
        (SolvableSylowOvergroups.of_equiv a.subgroupEquiv
          Atlas.G2.BinaryDerived.solvableSylowOvergroups)).elim
    | symmetric n hn a _ _ =>
      rcases hn with rfl | rfl
      · exact (FiveLocalFF.AlternatingSmall.not_proper_five S B hB hp a.subgroupEquiv).elim
      · exact Or.inr (.sevenDeleted hf hi a)
    | alternatingSix _ a _ _ =>
      exact (FiveLocalFF.AlternatingSmall.not_proper_six S B hB hp a.groupEquiv).elim
    | alternatingSeven _ _ a hd _ _ => exact Or.inr (.sevenFour hf hi a hd)
    | tripleSix _ a _ =>
      exact (FiveLocalFF.AlternatingSmall.not_proper_central_six S B hB hp a.quotientEquiv).elim
    | binaryLinear d hd _ a _ => exact Or.inr (.linear d hd hf hi a)
    | orthogonalSix _ _ a _ _ => exact Or.inr (.orthogonalSix hf hi a)
    | symmetricEight _ a _ => exact Or.inr (.symmetricEight hf hi a)
    | exteriorFive _ _ a hd _ _ => exact Or.inr (.exteriorFive hf hi a hd)
  | doubleThree F _ a _ _ =>
    exact Or.inl (.doubleThree F (containing_three_degree S B hB hp F a.groupEquiv) a)
  | naturalDual d hd _ hn => exact Or.inr (.naturalDual d hd hn)
  | repeatedNatural d r hd hr hb _ hn => exact Or.inr (.repeatedNatural d r hd hr hb hn)
/-- The surviving action markings identify actual A₇ or binary-linear actors. -/
theorem BinaryOrSevenAction.actor
    {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) Q V} {A : Subgroup Q} {s : MovedSection ρ A}
    (h : BinaryOrSevenAction s) :
    Nonempty (A ≃* alternatingGroup (Fin 7)) ∨
      ∃ d, (d = 4 ∨ d = 5) ∧ Nonempty (A ≃* SL(d,ZMod 2)) := by
  have eight (e : A ≃* alternatingGroup (Fin 8)) :
      Nonempty (A ≃* SL(4,ZMod 2)) :=
    ⟨(e.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two).trans
      (_root_.BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))⟩
  cases h with
  | sevenFour _ _ e _ => exact Or.inl ⟨e⟩
  | sevenDeleted _ _ e => exact Or.inl ⟨e.subgroupEquiv⟩
  | linear d hd _ _ e => exact Or.inr ⟨d,hd,⟨e.groupEquiv⟩⟩
  | orthogonalSix _ _ e => exact Or.inr ⟨4,Or.inl rfl,eight e.groupEquiv⟩
  | symmetricEight _ _ e => exact Or.inr ⟨4,Or.inl rfl,eight e.subgroupEquiv⟩
  | exteriorFive _ _ e _ => exact Or.inr ⟨5,Or.inr rfl,⟨e⟩⟩
  | naturalDual d hd e => exact Or.inr ⟨d,hd,⟨e.some.groupEquiv⟩⟩
  | repeatedNatural d r hd _ _ e => exact Or.inr ⟨d,hd,⟨e.some.groupEquiv⟩⟩

end CFSG.Quasithin.Chapter10.PointControl.Constrained
