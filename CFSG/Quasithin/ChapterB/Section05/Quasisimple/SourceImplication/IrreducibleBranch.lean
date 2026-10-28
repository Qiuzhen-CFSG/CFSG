module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.EasyCases
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.OuterNatural
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.NonsplitOffenders

/-!
# The source-correct irreducible branch of B.5.1

The original source hypothesis supplies normality of L. We apply the local
group reductions to every actual two-subgroup A of G; in particular these
apply to both LA in the reducible induction and LT in the irreducible branch.
No quotient-action faithfulness, offender containment or splitting is assumed.
The source observations α and β retain their literal ambient Sylow subgroup.

The local SQTK assertion needs `IrreducibleBranch.ContainsSimpleTwoGroups K`.
Observation α has exactly its stated local-offender-containment premise;
observation β has exactly the commutativity of the actual group `MulAut.Outer L`.
The irreducible-branch proof below discharges these local premises.

The source-correct companion in `IrreducibleBranch.SourceCatalogue` uses
ProjectiveLine's full B.4.2 list, with a two-dimensional F₄ subspace in the
triple-cover row. The old public one-dimensional contract is preserved.
`QuotientAction` proves faithfulness on L and every LA, and transports
irreducibility to the literal moved quotient. `LocalClassification` applies
the complete corrected B.4.2 input to LT with all hypotheses discharged.
`EasyCases` closes the J=L branch at ratio one or zero central kernel and
returns the full corrected B.5.1 irreducible alternative there.

`OuterNatural` proves the outer natural-action branch, including the Aut(A6)
exclusion. `NonsplitOffenders` completes the nonzero-central-kernel,
ratio-below-one branch using the genuine cohomology sieve and symplectic
normalizer calculation. Thus either G=L or G=LT with the specified natural
action. Applying the full corrected B.4.2 input to the ambient quotient now
gives L=F*(G), faithfulness and the complete marked catalogue on that quotient.
`QuasisimpleSourceHypothesis.irreducible_source_data` exposes these data, and
`irreducible_source_case` constructs the corrected B.5.1(1i) alternative.

Exact parameter inventory for this internal conditional branch: the complete
universal `SourceInduction.ProjectiveLine.IrreducibleClassificationInput` and
`ContainsSimpleTwoGroups K`, which asserts K-membership for every finite simple
two-group. All other premises are the original source hypothesis, the actual
moved section and its Irr⁺ condition. No cohomology, splitting, offender
containment or outer-action conclusion is an additional parameter. The source
assembly owner `qt-b05-quasisimple` must discharge the universal B.4.2 input
and instantiate the class condition; the remaining B.5.1 branches and clauses
belong to the full source-implication owner. The legacy interfaces are preserved.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1, printed
pp.99–100; B.4.2(8), p.86, and K.1.3, p.453.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : GroupClass.{u}} {L : Subgroup G}

/-- The actual LA reductions needed by both branches of B.5.1. -/
theorem QuasisimpleSourceHypothesis.local_group_reductions
    (h : QuasisimpleSourceHypothesis ρ K L)
    (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (A : Subgroup G) (hA : IsPGroup 2 A) :
    L.Normal ∧ Disjoint A (centralizer (L : Set G)) ∧
      pCore 2 ↥(L ⊔ A) = ⊥ ∧
      generalizedFitting ↥(L ⊔ A) = L.subgroupOf (L ⊔ A) ∧
      (generalizedFitting ↥(L ⊔ A)).map (L ⊔ A).subtype = L ∧
      IsSQTK K ↥(L ⊔ A) := by
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  exact ⟨inferInstance,
    IrreducibleBranch.twoSubgroup_disjoint_centralizer L A h.fitting h.twoCore hA,
    IrreducibleBranch.local_twoCore_eq_bot L (L ⊔ A) h.fitting h.twoCore le_sup_left,
    IrreducibleBranch.local_generalizedFitting L A h.fitting h.twoCore hA,
    IrreducibleBranch.local_generalizedFitting_map L A h.fitting h.twoCore hA,
    IrreducibleBranch.local_sqtk hK L A h.sqtk hA⟩

/-- Faithful conjugation, using the normality proof already derived from the source. -/
theorem QuasisimpleSourceHypothesis.twoSubgroup_conjugation_injective
    (h : QuasisimpleSourceHypothesis ρ K L)
    (A : Subgroup G) (hA : IsPGroup 2 A) :
    let _ : IsQuasisimple L := h.quasisimple
    let _ : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
    Function.Injective ((MulAut.conjNormal : G →* MulAut L).comp A.subtype) := by
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  exact IrreducibleBranch.twoSubgroup_conjugation_injective L A h.fitting h.twoCore hA

/-- Source observation α for the original finite faithful representation. -/
theorem QuasisimpleSourceHypothesis.alpha
    (h : QuasisimpleSourceHypothesis ρ K L) (T : Sylow 2 G)
    (hJT : generatedBy {A | IsBestOffender ρ A} T ≤ L) : L = ⊤ := by
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  exact IrreducibleBranch.whole_of_sylow_offenders_le ρ L T h.generated hJT

/-- Source observation β for every ambient Sylow two-subgroup. -/
theorem QuasisimpleSourceHypothesis.beta
    (h : QuasisimpleSourceHypothesis ρ K L)
    [IsMulCommutative (MulAut.Outer L)] (T : Sylow 2 G) : L ⊔ (T : Subgroup G) = ⊤ := by
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  exact IrreducibleBranch.whole_eq_component_sylow_of_outer_abelian ρ L h.fitting h.generated T

/-- All data of source B.5.1(1i), on the literal moved central quotient.
The complete corrected earlier B.4.2 implication is the only classification
parameter; both the outer and nonsplit branches are proved here. -/
theorem QuasisimpleSourceHypothesis.irreducible_source_data
    (h : QuasisimpleSourceHypothesis ρ K L)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u, v} K)
    (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (s : MovedSection ρ L) (hI : IsIrrPlus ρ L s.space.toSubmodule) :
    L = generalizedFitting G ∧ Function.Injective s.action ∧
      IsIrreducible (s.action.comp L.subtype) ∧
      SourceInduction.ProjectiveLine.IrreducibleActionCase s.action L
        (offenderSubgroup s.action) ∧
      (L = ⊤ ∨ (∀ T : Sylow 2 G, L ⊔ (T : Subgroup G) = ⊤) ∧
        OuterNaturalAction s.action) := by
  classical
  let := h.finite_module
  let T : Sylow 2 G := Classical.choice inferInstance
  have hc := IrreducibleBranch.local_classification earlier hK h s hI T
  have hext : L = ⊤ ∨ (∀ T' : Sylow 2 G, L ⊔ (T' : Subgroup G) = ⊤) ∧
      OuterNaturalAction s.action := by
    by_cases hJ : offenderSubgroup (s.action.comp (L ⊔ (T : Subgroup G)).subtype) =
        L.subgroupOf (L ⊔ (T : Subgroup G))
    · apply Or.inl
      by_cases hz : s.central.toSubmodule = ⊥
      · exact IrreducibleBranch.whole_of_central_eq_bot h s T hJ hz
      by_cases hq : quadraticRatio (s.action.comp (L ⊔ (T : Subgroup G)).subtype) = 1
      · exact IrreducibleBranch.whole_of_local_ratio_one h s T hJ hq
      obtain ⟨B, hB⟩ := IrreducibleBranch.local_bestOffender h s T
      have hle := (isFFModule_iff_quadraticRatio_le_one _).mp ⟨B, hB.isOffender _⟩
      exact IrreducibleBranch.whole_of_nonsplit_small_ratio h s hI T hc hJ hz
        (lt_of_le_of_ne hle hq)
    · exact Or.inr (IrreducibleBranch.outer_natural_of_local_offender_ne h s hI T hc hJ)
  have htop : L ⊔ (T : Subgroup G) = ⊤ := by
    rcases hext with hL | ⟨hLT, _⟩
    · rw [hL, top_sup_eq]
    · exact hLT T
  obtain ⟨hfit, hfaith, hcase⟩ :=
    IrreducibleBranch.ambient_classification_of_local_eq_top earlier hK h s hI
      T T.isPGroup' htop
  exact ⟨hfit, hfaith, IrreducibleBranch.moved_action_irreducible s hI, hcase, hext⟩

/-- Construct the full corrected irreducible alternative for the B.5.1
source-implication assembly, preserving every marked action and offender clause. -/
theorem QuasisimpleSourceHypothesis.irreducible_source_case
    (h : QuasisimpleSourceHypothesis ρ K L)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u, v} K)
    (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (s : MovedSection ρ L) (hI : IsIrrPlus ρ L s.space.toSubmodule) :
    L = generalizedFitting G ∧ SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s := by
  obtain ⟨hfit, hfaith, hirr, hcase, hext⟩ := h.irreducible_source_data earlier hK s hI
  exact ⟨hfit, .irreducible hI hfaith hirr hcase hext⟩

end CFSG.Quasithin.ChapterB.QuasisimpleSource
