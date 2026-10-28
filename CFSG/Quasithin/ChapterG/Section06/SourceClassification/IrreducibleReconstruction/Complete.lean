module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.IrreducibleReconstruction.Six
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.RankOneRows.SourceReduction
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.IrreducibleActors.Complete
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.SymplecticTwo
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.EndNodeRank

/-!
# Complete reconstruction of the irreducible G.6 source branch

The original involution has rank at most one on the literal central quotient,
so its cyclic subgroup is a best offender there. Its rank eliminates the G2,
alternating, and exterior-five rows; scalar degree eliminates larger fields.
Every remaining row is reconstructed on the original space by the preceding
linear and symmetric theorems, including both even permutation cores.
The ambient and central-Sylow conclusions are included in each surviving row.

Source: Aschbacher–Smith, G.6.4, printed pp.345–346, using B.4.2, p.86.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.QuasisimpleSource ChapterB.SourceInduction IrreducibleReconstruction
universe u v
private theorem symmetric_three_not_perfect : ¬ Group.IsPerfect (Equiv.Perm (Fin 3)) := by
  intro h
  let := h
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  have hs : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range
      (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype, ← alternatingGroup_eq_sign_ker]
  exact Group.IsPerfect.not_isSolvable _ hs

private theorem klein_seven_rank :
    rank (Subgroup.closure {ChapterB.Offenders.kleinFirst 7 (by decide),
      ChapterB.Offenders.kleinSecond 7 (by decide)}) = 2 := by
  let A := Subgroup.closure {ChapterB.Offenders.kleinFirst 7 (by decide),
    ChapterB.Offenders.kleinSecond 7 (by decide)}
  let : IsKleinFour A := isKleinFour_closure_pair _ _ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by change _ * _ = _ * _; decide)
  rw [rank, IsKleinFour.card_four]
  decide

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {κ : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}
theorem Hypotheses.conclusion_of_irreducible_source
    (h : Hypotheses κ ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (hh : IrreducibleQuasisimpleRemainder ρ a) : Conclusion ρ a := by
  classical
  let := h.finite_group
  let := h.finite_module
  obtain ⟨hq, d, hs, hi, hf, hir, hcase⟩ := hh
  let K := normalClosure ({a} : Set G)
  let L := generalizedFitting K
  let τ : Representation (ZMod 2) K
      (d.sectionData.space.toSubmodule ⧸ d.sectionData.central.toSubmodule) :=
    d.sectionData.central.quotientRepresentation
  let t : K := ⟨a, subset_normalClosure (Set.mem_singleton a)⟩
  have htne : t ≠ 1 := fun he => h.nonidentity (congrArg Subtype.val he)
  have htp : t ^ 2 = 1 := Subtype.ext h.involution
  have hcost : Module.finrank (ZMod 2)
      (LinearMap.range (τ t - LinearMap.id)) ≤ 1 :=
    (subquotient_displacement_rank_le (ρ.comp K.subtype)
      d.sectionData.space d.sectionData.central t).trans ht.le
  have hb := bestOffender_of_involution_displacement_le_one
    τ t htp htne hcost
  have htr : rank (zpowers t) = 1 := by
    rw [rank, Nat.card_zpowers, orderOf_eq_prime htp htne]
    decide
  cases hcase with
  | linearTwo F whole e _ _ =>
    let E := actionOfTop whole.symm e
    have hF := model_field_degree_one_of_rank_one F hf t htne hcost (specialLinearNatural 2) E
    let B := E.groupEquiv.trans
      ((ExtensionConsequences.degreeOneNaturalEquiv F hF 2).groupEquiv.trans
        ((BinaryLinear.OuterCyclic.slEquivLinear 2).trans
          BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree))
    let : Group.IsPerfect L := hq.toIsPerfect
    let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
      (f := ((MulEquiv.subgroupCongr whole.symm).trans topEquiv).toMonoidHom)
      ((MulEquiv.subgroupCongr whole.symm).trans topEquiv).surjective
    exact (symmetric_three_not_perfect
      (Group.IsPerfect.ofSurjective (f := B.toMonoidHom) B.surjective)).elim
  | linearThree F whole e _ =>
    let E := actionOfTop whole.symm e
    have hF := model_field_degree_one_of_rank_one F hf t htne hcost (specialLinearNatural 3) E
    let B := ExtensionConsequences.degreeOneNaturalEquiv F hF 3
    exact h.conclusion_of_linearThree_section ht d.sectionData hs
      ⟨E.groupEquiv.trans B.groupEquiv, E.linearEquiv.trans B.linearEquiv,
        fun g v => (congrArg B.linearEquiv (E.intertwines g v)).trans (B.intertwines _ _)⟩
  | symplectic F large whole e _ =>
    have hF := model_field_degree_one_of_rank_one F hf t htne hcost (symplecticNatural 2)
      (actionOfTop whole.symm e)
    omega
  | symplecticTwo e _ =>
    exact h.conclusion_of_symplecticTwo_section ht d.sectionData hs e
  | g2 F _ _ _ hoff _ => have := hoff (zpowers t) hb; have := F.degree_pos; omega
  | g2Two _ hoff _ => have := hoff (zpowers t) hb; omega
  | symmetric n hn e _ _ =>
    exact h.conclusion_of_symmetricOdd_section ht d.sectionData hs hi hn e
  | alternatingSix _ _ hoff _ => have := (hoff (zpowers t) hb).1; omega
  | alternatingSeven whole _ e _ hoff _ =>
    obtain ⟨g, hg⟩ := hoff (zpowers t) hb
    have he := congrArg rank hg
    have hfi : Function.Injective ((alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom) := by
      intro x y hh
      exact e.injective (Subtype.ext hh)
    rw [rank_map_injective _ hfi,
      rank_subgroupOf (show zpowers t ≤ generalizedFitting K by rw [← whole]; exact le_top), htr,
      rank_map_injective _ (MulAut.conj (g : Equiv.Perm (Fin 7))).injective, klein_seven_rank] at he
    omega
  | tripleSix whole action _ =>
    have he := Nat.card_congr (Subgroup.centerCongr
      ((MulEquiv.subgroupCongr whole.symm).trans topEquiv)).toEquiv
    rw [Nat.card_congr action.centerEquiv.toEquiv, h.normalClosure_center_eq_bot ht] at he
    norm_num at he
  | binaryLinear n hn whole e _ =>
    exact h.conclusion_of_binaryLinear_section d.sectionData hs hi whole.symm
      (by rcases hn with rfl | rfl <;> decide) (by rcases hn with rfl | rfl <;> decide) e
  | orthogonalSix _ _ _ hoff _ => have := hoff (zpowers t) hb; omega
  | symmetricEight _ e _ =>
    exact h.conclusion_of_symmetricEight_section ht d.sectionData hs e
  | exteriorFive whole _ e _ hoff _ =>
    have he := IsEndNodeRadical.rank (hoff (zpowers t) hb)
    rw [rank_map_injective _ e.injective,
      rank_subgroupOf (show zpowers t ≤ generalizedFitting K by rw [← whole]; exact le_top),
      htr] at he
    omega
end CFSG.Quasithin.ChapterG.Section06
