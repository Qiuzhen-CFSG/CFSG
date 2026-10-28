module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionQuotient
public import Theory.Representation.BinaryOffender.TwoSectionBudget

/-!
# A faithful component actor on the two literal orbit sections

If a normal quasisimple component generates the whole module, its action on
any proper invariant quotient is nontrivial. The kernels on a noncentral
invariant subspace and its quotient therefore centralize the component.
An elementary actor faithful on that component is faithful on both sections.
Their fixed codimensions share the original actor's budget, so a budget of
twice its rank makes its actual image an FF offender on at least one section.

The application in `SeedAlternativesMovedExhaustionSections` keeps the local
actor image of LT on U and the literal quotient U/W. This supplies the
faithful-actor section alternative needed in D.3.9(1) and D.3.13. The model
exclusions and final source325 assembly remain with qt-baumann-fsu.
Source: Aschbacher--Smith D.3.9(1), D.3.13, printed pp.199--202.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
  (ρ : Representation (ZMod 2) H E)

/-- Faithfulness on the component gives faithfulness on both actual sections,
without assuming faithfulness of the component on either section. -/
theorem faithful_sections_of_component_centralizer_eq_bot
    (K : Subgroup H) [K.Normal] [IsQuasisimple K]
    (hfull : subspaceCommutator ρ ⊤ K = ⊤)
    (I : Submodule (ZMod 2) E) (hKI : K ≤ subspaceStabilizer ρ I)
    (hIn : ¬ I ≤ fixedSpace ρ K) (hne : I ≠ ⊤)
    (P : Subgroup H) (hPI : P ≤ subspaceStabilizer ρ I)
    (A : Subgroup H) (hAC : A ⊓ centralizer (K : Set H) = ⊥) :
    let S := invariantSubspace ρ P I hPI
    (∀ a ∈ A.subgroupOf P, (∀ v, S.toRepresentation a v = v) → a = 1) ∧
    (∀ a ∈ A.subgroupOf P, (∀ v, S.quotientRepresentation a v = v) → a = 1) := by
  let S := invariantSubspace ρ P I hPI
  constructor
  · intro a ha hf
    have hc : a.val ∈ centralizer (K : Set H) :=
      subspaceKernel_le_component_centralizer ρ K I hKI hIn A
        ⟨ha,fun v hv => congrArg Subtype.val (hf ⟨v,hv⟩)⟩
    apply Subtype.ext
    exact hAC.le ⟨ha,hc⟩
  · intro a ha hf
    have hk := quotient_kernel_le_component_centralizer ρ K hfull I hKI hne
    have hc : a.val ∈ centralizer (K : Set H) := by
      apply hk
      refine ⟨⟨a.val,hPI a.property⟩,?_,rfl⟩
      apply LinearMap.ext
      exact hf
    apply Subtype.ext
    exact hAC.le ⟨ha,hc⟩

variable [FiniteDimensional (ZMod 2) E]

/-- One of the two literal images of the same elementary actor is an FF offender.
No independently chosen offender or multiplicity bound is used. -/
theorem offender_section_or_quotient_of_faithful_component_actor
    (K : Subgroup H) [K.Normal] [IsQuasisimple K]
    (hfull : subspaceCommutator ρ ⊤ K = ⊤)
    (I : Submodule (ZMod 2) E) (hKI : K ≤ subspaceStabilizer ρ I)
    (hIn : ¬ I ≤ fixedSpace ρ K) (hne : I ≠ ⊤)
    (P : Subgroup H) (hPI : P ≤ subspaceStabilizer ρ I)
    (A : Subgroup H) (hAP : A ≤ P) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : A ⊓ centralizer (K : Set H) = ⊥) :
    let S := invariantSubspace ρ P I hPI
    let B := A.subgroupOf P
    IsOffender (imageRepresentation S.toRepresentation) (actionSubgroup S.toRepresentation B) ∨
      IsOffender (imageRepresentation S.quotientRepresentation)
        (actionSubgroup S.quotientRepresentation B) := by
  classical
  let S := invariantSubspace ρ P I hPI
  let B := A.subgroupOf P
  let : IsElementaryAbelian 2 A := hA.2
  have hB : IsElementaryTwo B := by
    refine ⟨?_, IsElementaryAbelian.subgroupOf hAP⟩
    intro hz
    apply hA.1
    change A.subgroupOf P = ⊥ at hz
    rw [← map_subgroupOf_eq_of_le hAP, hz, Subgroup.map_bot]
  have hf := faithful_sections_of_component_centralizer_eq_bot
    ρ K hfull I hKI hIn hne P hPI A hAC
  have hb := fixedCodim_quotient_add_subrepresentation_le (ρ.comp P.subtype) S B
  have hbudget : fixedCodim (ρ.comp P.subtype) B ≤ 2 * rank B := by
    simpa only [B, rank_subgroupOf hAP, fixedCodim_subgroupOf ρ hAP] using hsmall
  by_cases hs : fixedCodim S.toRepresentation B ≤ rank B
  · left
    refine ⟨hB.actionSubgroup S.toRepresentation hf.1, ?_⟩
    rwa [fixedCodim_actionSubgroup, actionSubgroup_rank S.toRepresentation B hf.1]
  · right
    refine ⟨hB.actionSubgroup S.quotientRepresentation hf.2, ?_⟩
    rw [fixedCodim_actionSubgroup, actionSubgroup_rank S.quotientRepresentation B hf.2]
    change fixedCodim S.quotientRepresentation B ≤ rank B
    omega
end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
