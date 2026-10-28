module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.ClassifiedSections
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Preparation.Contracts
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.SpecificGroups.SymplecticFour.Binary.FieldTransport
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Converting the B.5.5 component models

The ordinary group alternatives of B.5.5 give the Lie and alternating
alternatives used in 15.3.49(l). Quasisimplicity excludes SL₂(2), which is
solvable. The triple-cover branch deliberately retains its actual module
section as a separate premise; a group isomorphism alone cannot supply it.

Source: Aschbacher–Smith, B.5.5(1)(iv), printed pp.104–105, and 15.3.49(l),
printed p.1144, combined manuscript of 1 March 2004.
-/

public section
open Subgroup Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
open ComponentReduction ModelReduction BinaryModels ModelSieve
open ChapterB.QuasisimpleSource
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) (C : Subgroup D)

/-- The linear rank-one branch has field order at least four. -/
theorem componentSection_linearTwo [IsQuasisimple C] (F : BinaryField) (e : C ≃* SL(2,F.Carrier)) :
    ComponentSectionAlternative ρ C := by
  have hdegree : 2 ≤ F.degree := by
    by_contra h
    have h1 : F.degree = 1 := by have := F.degree_pos; omega
    let f := Theory.SpecificGroups.SymplecticFour.Binary.fieldEquivZModTwo F.Carrier
      (by simpa [h1] using F.card_eq)
    let a := e.trans ((Atlas.fieldEquivSL 2 f).trans
      ((BinaryLinear.OuterCyclic.slEquivLinear 2).trans
        BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree))
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
      let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
      apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
    let : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective
      (f := a.toMonoidHom) a.injective
    let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
    let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
    exact Group.IsPerfect.not_isSolvable C inferInstance
  exact .lie F.degree (.linear_two hdegree F.Carrier F.card_eq
    ⟨e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL⟩)

/-- The linear rank-two branch keeps the defining binary field. -/
theorem componentSection_linearThree (F : BinaryField) (e : C ≃* SL(3,F.Carrier)) :
    ComponentSectionAlternative ρ C :=
  .lie F.degree (.linear_three F.degree_pos F.Carrier F.card_eq ⟨e⟩)

/-- The symplectic branch includes its derived binary endpoint. -/
theorem componentSection_symplectic (F : BinaryField)
    (e : C ≃* commutator (Matrix.symplecticGroup (Fin 2) F.Carrier)) :
    ComponentSectionAlternative ρ C :=
  .lie F.degree (.symplectic F.degree_pos F.Carrier F.card_eq ⟨e⟩)

/-- The G₂ branch includes its derived binary endpoint. -/
theorem componentSection_g2 (F : BinaryField)
    (e : C ≃* commutator (Atlas.G2.Model F.Carrier)) :
    ComponentSectionAlternative ρ C :=
  .lie F.degree (.g2 F.degree_pos F.Carrier F.card_eq ⟨e⟩)

/-- Binary special and projective special linear groups agree here. -/
theorem componentSection_binaryLinear (n : ℕ) (hn : n = 4 ∨ n = 5)
    (e : C ≃* SL(n,ZMod 2)) : ComponentSectionAlternative ρ C :=
  .lie 1 (.binary_linear rfl n hn
    ⟨e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0 < n)).symm⟩)

/-- Only the cubic-center alternative needs additional representation data. -/
theorem componentSection_of_models [IsQuasisimple C]
    (h : ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.Preparation.ComponentModels C)
    (hhex : Nat.card (center C) = 3 → ComponentSectionAlternative ρ C) :
    ComponentSectionAlternative ρ C := by
  rcases h with ⟨F, ⟨e⟩⟩ | ⟨F, ⟨e⟩⟩ | ⟨F, ⟨e⟩⟩ | ⟨F, ⟨e⟩⟩ | h | ⟨⟨e⟩, _⟩ | ⟨e⟩ | ⟨e⟩
  · exact componentSection_linearTwo ρ C F e
  · exact componentSection_linearThree ρ C F e
  · exact componentSection_symplectic ρ C F e
  · exact componentSection_g2 ρ C F e
  · exact .alternating_seven h
  · apply hhex
    rw [Nat.card_congr e.toEquiv]
    simp
  · obtain ⟨e⟩ := e
    exact componentSection_binaryLinear ρ C 4 (Or.inl rfl) e
  · obtain ⟨e⟩ := e
    exact componentSection_binaryLinear ρ C 5 (Or.inr rfl) e

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
