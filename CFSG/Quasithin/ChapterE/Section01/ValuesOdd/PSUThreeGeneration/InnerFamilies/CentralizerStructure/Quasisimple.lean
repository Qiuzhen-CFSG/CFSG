module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerActors
public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleRadicalTwoExtension
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure

/-!
# The literal E₂ clauses for a quasisimple two-extension

The normal component has a simple image modulo the actual solvable radical.
That image is the entire layer and has two-group quotient. Normality makes
its local-tau orbit a single component. Every actor with nontrivial image
has full commutator with it, by faithfulness and the simple-normal dichotomy.
The radical and both residuals are calculated on the original local carrier.

This is a conditional constructor; the PSU₃ application must establish the
component model and prove that its inner four-group survives the radical.
Source: Aschbacher--Smith E.1.2(E2), printed p.210.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration
variable {G : Type*} [Group G] [Finite G]

/-- A normal quasisimple subgroup with two-group center and quotient supplies
all E₂ clauses once the actor is proved nontrivial modulo the actual radical. -/
theorem eCaseComponent_of_quasisimple_two_quotient (T A K : Subgroup G)
    (D : Subgroup K) [D.Normal] [IsQuasisimple D]
    (hz : IsPGroup 2 (center D)) (hq : IsPGroup 2 (K ⧸ D))
    (hne : ¬ A.subgroupOf K ≤ solvableRadical K) :
    CFSG.Quasithin.ChapterE.ECaseComponent T A K := by
  let Q := K ⧸ solvableRadical K
  let q := QuotientGroup.mk' (solvableRadical K)
  let C := D.map q
  let : C.Normal := (inferInstance : D.Normal).map q (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup (D ⧸ solvableRadical D) := quasisimple_radicalQuotient_isSimple D
  let : Group.IsPerfect (D ⧸ solvableRadical D) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  let e := normalRadicalQuotientEquivImage D
  let : IsSimpleGroup C := e.symm.isSimpleGroup
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := q.subgroupMap D) (q.subgroupMap_surjective D)
  have hc : center C = ⊥ := by
    rcases (inferInstance : (center C).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative C (center_eq_top_iff.mp h)).elim
  let : IsQuasisimple C := ⟨((QuotientGroup.quotientMulEquivOfEq hc).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  have hqC : IsPGroup 2 (Q ⧸ C) := normal_radical_image_two_quotient D hq
  have hcomp : IsComponent Q C := ⟨(inferInstance : C.Normal).isSubnormal, inferInstance⟩
  obtain ⟨hlayer, _, _⟩ := SimpleSocle.layer_residuals C hqC
  obtain ⟨_, hp, hs⟩ := SimpleSocle.layer_residuals D hq
  have hR := radical_isTwoGroup_of_quasisimple_two_quotient D hz hq
  have hclosed : CFSG.Quasithin.ChapterE.IsTwoClosed (solvableRadical K) := by
    obtain ⟨S, hS⟩ := (hR.to_subgroup ⊤).exists_le_sylow
    have he : (S : Subgroup (solvableRadical K)) = ⊤ := top_unique hS
    exact ⟨S, he ▸ inferInstance⟩
  have hcore : pCore 2 Q = ⊥ :=
    SimpleSocle.pCore_eq_bot solvableRadical_quotient_solvableRadical 2
  have hcentral := centralizer_eq_bot_of_simple_two_quotient C
    (Group.IsPerfect.not_isMulCommutative C) hqC hcore
  have ha : (A.subgroupOf K).map q ≠ ⊥ := by
    intro he
    exact hne (by simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp he)
  refine ⟨hclosed, ?_, hp.trans hs.symm, C, hcomp, ?_, Or.inl ?_⟩
  · rw [hlayer]
    exact ⟨inferInstance, hqC⟩
  · rw [CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankOneUpper.conjugateJoin_eq_of_normal,
      hlayer]
  · exact SimpleSocle.commutator_eq C hcentral _ ha

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration
