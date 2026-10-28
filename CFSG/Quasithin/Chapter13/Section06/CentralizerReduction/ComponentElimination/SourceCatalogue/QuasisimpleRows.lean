module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.Models
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.BinaryThree
public import Theory.Representation.HexacodeAction.CoverRecognition
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary

/-!
# The component catalogue in the quasisimple B.5.1 branch

Extract the actual component group from every B.5.1 action alternative.
The triple-six row is identified with the concrete perfect hexacode cover,
and both eight-point rows with PSL₄(2). The output retains rank-one and
larger-field models for the original 13.6.18–19 exclusions; the remaining
entries are precisely the reduced catalogue used in 13.6.20.

Source: Aschbacher–Smith B.5.1 and the paragraph before 13.6.20,
printed pp.99–103 and 931, combined manuscript of 1 March 2004.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceCatalogue
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
open SourceContainment.RankTwo

/-- The exact field alternatives eliminated in 13.6.18–19, or one of
its seven surviving concrete group models. -/
inductive Model (Q : Type*) [Group Q] : Prop
  | linearTwo (F : BinaryField) (iso : Nonempty (Q ≃* PSL(2,F.Carrier)))
  | linearThree (F : BinaryField) (large : 1 < F.degree)
      (iso : Nonempty (Q ≃* SL(3,F.Carrier)))
  | symplectic (F : BinaryField) (large : 1 < F.degree)
      (iso : Nonempty (Q ≃* Matrix.symplecticGroup (Fin 2) F.Carrier))
  | g2 (F : BinaryField) (large : 1 < F.degree)
      (iso : Nonempty (Q ≃* Atlas.G2.Model F.Carrier))
  | reduced (model : ReducedModel Q)

theorem ReducedModel.transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : ReducedModel A) : ReducedModel B := by
  cases h with
  | linear n hn f => exact .linear n hn (f.map fun f => e.symm.trans f)
  | symplectic f => exact .symplectic (f.map fun f => e.symm.trans f)
  | g2 f => exact .g2 (f.map fun f => e.symm.trans f)
  | ahat6 f => exact .ahat6 (f.map fun f => e.symm.trans f)
  | a7 f => exact .a7 (f.map fun f => e.symm.trans f)

theorem Model.transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : Model A) : Model B := by
  cases h with
  | linearTwo F f => exact .linearTwo F (f.map fun f => e.symm.trans f)
  | linearThree F hn f => exact .linearThree F hn (f.map fun f => e.symm.trans f)
  | symplectic F hn f => exact .symplectic F hn (f.map fun f => e.symm.trans f)
  | g2 F hn f => exact .g2 F hn (f.map fun f => e.symm.trans f)
  | reduced h => exact .reduced (ReducedModel.transport e h)

theorem Model.of_linearThree {Q : Type*} [Group Q]
    (F : BinaryField) (e : Q ≃* SL(3,F.Carrier)) : Model Q := by
  by_cases hF : F.degree = 1
  · exact .reduced (.linear 3 ⟨le_rfl,by decide⟩
      ⟨e.trans ((ExtensionConsequences.degreeOneNaturalEquiv F hF 3).groupEquiv.trans
        (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide)).symm)⟩)
  · exact .linearThree F (by have := F.degree_pos; omega) ⟨e⟩

theorem Model.of_alternatingFive {Q : Type*} [Group Q]
    (e : Q ≃* alternatingGroup (Fin 5)) : Model Q :=
  .linearTwo BinaryField.four ⟨e.trans
    (Atlas.Comparisons.Exceptional.psl2Card4EquivAlt5
      (show Nat.card BinaryField.four.Carrier = 4 by
        rw [BinaryField.four.card_eq]; decide)).symm⟩

theorem Model.of_alternatingSix {Q : Type*} [Group Q]
    (e : Q ≃* alternatingGroup (Fin 6)) : Model Q :=
  .reduced (.symplectic ⟨e.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
      (F := ZMod 2) (by simp)).symm⟩)

private theorem model_of_binaryLinear {Q : Type*} [Group Q]
    {n : ℕ} (hn : n = 4 ∨ n = 5) (e : Q ≃* SL(n,ZMod 2)) : Model Q :=
  .reduced (.linear n (by rcases hn with rfl | rfl <;> omega)
    ⟨e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega)).symm⟩)

private theorem model_of_alternatingEight {Q : Type*} [Group Q]
    (e : Q ≃* alternatingGroup (Fin 8)) : Model Q :=
  .reduced (.linear 4 ⟨by decide,by decide⟩
    ⟨e.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm⟩)

private theorem tripleSix_equiv {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {C : Subgroup D} [IsQuasisimple C]
    (h : ProjectiveLine.TripleSixAction ρ C) :
    Nonempty (C ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  let f := h.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (center C))
  have hk : f.ker = center C := by
    rw [MonoidHom.ker_comp_of_injective _ _ h.quotientEquiv.injective,
      QuotientGroup.ker_mk']
  obtain ⟨e,_⟩ := Representation.Hexacode.triple_cover_equiv f
    (h.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _))
    hk.le (by rw [hk,Nat.card_congr h.centerEquiv.toEquiv]; simp)
  exact ⟨e⟩

/-- Every irreducible B.5.1 row gives the actual component model. -/
theorem model_of_irreducible {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {C H : Subgroup D} [IsQuasisimple C]
    (h : ProjectiveLine.IrreducibleActionCase ρ C H) : Model C := by
  cases h with
  | linearTwo F _ e _ _ => exact .linearTwo F ⟨e.groupEquiv.trans
      Atlas.RankOneFieldAutomorphisms.slEquivPSL⟩
  | linearThree F _ e _ => exact Model.of_linearThree F e.groupEquiv
  | symplectic F hn _ e _ => exact .symplectic F hn ⟨e.groupEquiv⟩
  | symplecticTwo e _ => exact .reduced (.symplectic ⟨e.subgroupEquiv⟩)
  | g2 F hn _ e _ _ => exact .g2 F hn ⟨e.groupEquiv⟩
  | g2Two e _ _ => exact .reduced (.g2 ⟨e.subgroupEquiv⟩)
  | symmetric n hn e _ _ =>
    rcases hn with rfl | rfl
    · exact Model.of_alternatingFive e.subgroupEquiv
    · exact .reduced (.a7 ⟨e.subgroupEquiv⟩)
  | alternatingSix _ e _ _ => exact Model.of_alternatingSix e.groupEquiv
  | alternatingSeven _ _ e _ _ _ => exact .reduced (.a7 ⟨e⟩)
  | tripleSix _ h _ => exact .reduced (.ahat6 (tripleSix_equiv h))
  | binaryLinear n hn _ e _ => exact model_of_binaryLinear hn e.groupEquiv
  | orthogonalSix _ _ e _ _ => exact model_of_alternatingEight e.groupEquiv
  | symmetricEight _ e _ => exact model_of_alternatingEight e.subgroupEquiv
  | exteriorFive _ _ e _ _ _ => exact model_of_binaryLinear (Or.inr rfl) e

/-- The full B.5.1 conclusion gives the group catalogue, including repeated
and natural-plus-dual actions without any splitting assumption. -/
theorem model_of_quasisimple {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {C : Subgroup D} [IsQuasisimple C]
    (h : ProjectiveLine.QuasisimpleSourceConclusion ρ C) : Model C := by
  cases h.clause_one with
  | irreducible _ _ _ hc _ => exact model_of_irreducible hc
  | doubleThree F _ e _ _ => exact Model.of_linearThree F e.groupEquiv
  | naturalDual n hn _ e => exact model_of_binaryLinear hn e.some.groupEquiv
  | repeatedNatural n r hn _ _ _ e => exact model_of_binaryLinear hn e.some.groupEquiv

/-- The proved 13.6.18–19 exclusions remove every field alternative. -/
theorem Model.reduced_of_field_exclusions {Q : Type*} [Group Q] (h : Model Q)
    (h2 : ∀ F : BinaryField, ¬ Nonempty (Q ≃* PSL(2,F.Carrier)))
    (h3 : ∀ F : BinaryField, 1 < F.degree → ¬
      (Nonempty (Q ≃* SL(3,F.Carrier)) ∨
        Nonempty (Q ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) ∨
        Nonempty (Q ≃* Atlas.G2.Model F.Carrier))) : ReducedModel Q := by
  cases h with
  | linearTwo F e => exact (h2 F e).elim
  | linearThree F hn e => exact (h3 F hn (Or.inl e)).elim
  | symplectic F hn e => exact (h3 F hn (Or.inr (Or.inl e))).elim
  | g2 F hn e => exact (h3 F hn (Or.inr (Or.inr e))).elim
  | reduced h => exact h

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceCatalogue
