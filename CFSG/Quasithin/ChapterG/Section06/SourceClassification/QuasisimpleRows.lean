module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.Sections
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.CubicRestriction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.LargerFieldThree.AxisFourGeometry.Conjugacy

/-!
# Selecting the genuine irreducible action in the quasisimple branch

The original cyclic rank-one offender cannot be a full SL3 axis group: the
latter has rank twice the defining-field degree. This excludes the doubled
SL3 row. The original normalized and inverted cubic belongs to the normal
closure, whose literal Sylow intersection still normalizes it. The binary
linear actor sieve then excludes every natural-plus-dual or repeated SL4/SL5
row, without reconstructing a fixed-space extension.

The remaining B.5.1 row retains the exact faithful central quotient action,
its irreducibility, and the full corrected B.4 action list. Its moved space is
V and its offender actor is the entire normal closure, as proved in Sections.
Source: Aschbacher–Smith, C.5.12, p.163, and G.6.4, pp.345–346.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
open CFSG.Quasithin.ChapterK.Linear.Natural
open ChapterB.NaturalExtensions.LargerFieldThree
universe u v

private theorem fullAxis_rank (F : BinaryField) {A : Subgroup SL(3,F.Carrier)}
    (hA : IsFullAxisGroup F 3 A) : rank A = 2 * F.degree := by
  obtain ⟨s, hs⟩ := AxisFourGeometry.full_axis_conjugate_standard F hA
  rw [← rank_map_injective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective A,
    hs, hyperplaneCentralizer_rank]
  omega

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {κ : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

theorem Hypotheses.quasisimple_irreducible_of_normalized_cubic
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (S : Sylow 2 G) (c : G) (hc : c ^ 3 = 1) (hcne : c ≠ 1)
    (hi : a * c = c ^ 2 * a)
    (hn : (S : Subgroup G) ≤ normalizer (zpowers c : Set G))
    (hq : IsQuasisimple (generalizedFitting (normalClosure ({a} : Set G))))
    (d : ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (normalClosure ({a} : Set G)).subtype)
      (generalizedFitting (normalClosure ({a} : Set G)))) :
    d.sectionData.space.toSubmodule = ⊤ ∧
    IsIrrPlus (ρ.comp (normalClosure ({a} : Set G)).subtype)
      (generalizedFitting (normalClosure ({a} : Set G))) d.sectionData.space.toSubmodule ∧
    Function.Injective d.sectionData.action ∧
    IsIrreducible (d.sectionData.action.comp
      (generalizedFitting (normalClosure ({a} : Set G))).subtype) ∧
    ProjectiveLine.IrreducibleActionCase d.sectionData.action
      (generalizedFitting (normalClosure ({a} : Set G))) ⊤ := by
  classical
  let := h.finite_group
  let := h.finite_module
  refine ⟨h.rank_one_quasisimple_section_top ht hq d.sectionData, ?_⟩
  let K := normalClosure ({a} : Set G)
  let L := generalizedFitting K
  let σ := ρ.comp K.subtype
  let t : K := ⟨a, subset_normalClosure (Set.mem_singleton a)⟩
  have htp : t ^ 2 = 1 := Subtype.ext h.involution
  have htne : t ≠ 1 := fun he => h.nonidentity (congrArg Subtype.val he)
  have hcost : Module.finrank (ZMod 2)
      (LinearMap.range (d.sectionData.space.toRepresentation t - LinearMap.id)) ≤ 1 := by
    have hh := fixedCodim_subrepresentation_le σ d.sectionData.space (zpowers t)
    simp only [fixedCodim_zpowers_eq_displacement_rank] at hh
    exact hh.trans ht.le
  have hb := bestOffender_of_involution_displacement_le_one
    d.sectionData.space.toRepresentation t htp htne hcost
  have htr : rank (zpowers t) = 1 := by
    rw [rank, Nat.card_zpowers, orderOf_eq_prime htp htne]
    decide
  cases d.clause_one with
  | irreducible hip hf hir hs _ =>
    refine ⟨hip, hf, hir, ?_⟩
    rwa [h.normalClosure_section_generated ht d.sectionData] at hs
  | doubleThree F whole e hoff _ =>
    have haxis := (hoff (zpowers t)).mp hb
    have hr := fullAxis_rank F haxis
    rw [rank_map_injective _ e.groupEquiv.injective,
      rank_subgroupOf (show zpowers t ≤ generalizedFitting (normalClosure ({a} : Set G)) by rw [whole]; exact le_top), htr] at hr
    have hp := F.degree_pos
    omega
  | naturalDual n hnd whole he =>
    obtain ⟨e⟩ := he
    let E := (topEquiv.symm.trans (MulEquiv.subgroupCongr whole.symm)).trans
      (e.groupEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear n))
    have hd := binary_normalClosure_degree_of_normalized_inverted_cubic a c S hc hcne hi hn
      (show 2 ≤ n by rcases hnd with rfl | rfl <;> decide) E
    rcases hnd with rfl | rfl <;> omega
  | repeatedNatural n r hnd _ _ whole he =>
    obtain ⟨e⟩ := he
    let E := (topEquiv.symm.trans (MulEquiv.subgroupCongr whole.symm)).trans
      (e.groupEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear n))
    have hd := binary_normalClosure_degree_of_normalized_inverted_cubic a c S hc hcne hi hn
      (show 2 ≤ n by rcases hnd with rfl | rfl <;> decide) E
    rcases hnd with rfl | rfl <;> omega
end CFSG.Quasithin.ChapterG.Section06
