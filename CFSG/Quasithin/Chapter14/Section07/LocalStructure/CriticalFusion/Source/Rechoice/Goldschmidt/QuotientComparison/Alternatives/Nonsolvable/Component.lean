module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable.SmallImage
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# Identifying the small image with the actual component

A noncommutative subnormal subgroup contains a quasisimple generalized
Fitting subgroup: otherwise component dichotomy and self-centralization
would make it abelian. Solvability excludes the S₃ case. In either simple
case, normality and nontriviality identify the actual component with the
original embedded small subgroup, retaining its isomorphism.

Source: Aschbacher–Smith, Lemma 14.7.70, printed p.1075, with the
quasisimple reduction in the proof of F.6.18, printed pp.309–310.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable

private theorem simple_SL : IsSimpleGroup Matrix.PSL3Two.SL := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  exact Matrix.PSL3Two.equiv.isSimpleGroup

private theorem perfect_SL : Group.IsPerfect Matrix.PSL3Two.SL := Atlas.sl_perfect 3 (by decide)

private theorem perfect_five : Group.IsPerfect (alternatingGroup (Fin 5)) :=
  ⟨commutator_alternatingGroup_eq_top (by simp)⟩

private theorem symmetricThree_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
  rw [range_subtype, ← alternatingGroup_eq_sign_ker]

private theorem commutative_of_equiv {A B : Type*} [Group A] [Group B]
    [IsMulCommutative A] (e : A ≃* B) : IsMulCommutative B := by
  refine ⟨⟨fun x y => ?_⟩⟩
  apply e.symm.injective
  simp only [map_mul, mul_comm]

theorem SmallModel.not_commutative {K : Type*} [Group K] (h : SmallModel K) :
    ¬ IsMulCommutative K := by
  intro hc
  let := hc
  rcases h with he | he | he <;> obtain ⟨e⟩ := he
  · have hh : IsMulCommutative (Equiv.Perm (Fin 3)) := (commutative_of_equiv e)
    have := Equiv.Perm.isMulCommutative_iff_card_le_two.mp hh
    norm_num at this
  · let := simple_SL
    let := perfect_SL
    exact Group.IsPerfect.not_isMulCommutative Matrix.PSL3Two.SL (commutative_of_equiv e)
  · let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    let := perfect_five
    exact Group.IsPerfect.not_isMulCommutative (alternatingGroup (Fin 5)) (commutative_of_equiv e)

variable {D : Type*} [Group D] [Finite D]

/-- A noncommutative subnormal subgroup contains the quasisimple F*. -/
theorem fitting_le_small (K : Subgroup D) (hK : K.IsSubnormal) (hm : SmallModel K)
    (hq : IsQuasisimple (generalizedFitting D)) : generalizedFitting D ≤ K := by
  let := hq
  have hcomp : IsComponent D (generalizedFitting D) :=
    ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal, hq⟩
  rcases hcomp.subnormal_dichotomy K hK with he | hc
  · exact he
  · have hKC : K ≤ centralizer (generalizedFitting D : Set D) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
    have hKQ : K ≤ generalizedFitting D := hKC.trans (centralizer_generalizedFitting_le D)
    exact (hm.not_commutative (le_centralizer_iff_isMulCommutative.mp
      (hKC.trans (centralizer_le hKQ)))).elim

/-- In a simple small model the component equals the original embedded subgroup. -/
private theorem fitting_eq_small_simple (K : Subgroup D) (hK : K.IsSubnormal)
    (hm : SmallModel K) (hq : IsQuasisimple (generalizedFitting D)) [IsSimpleGroup K] :
    generalizedFitting D = K := by
  have hl := fitting_le_small K hK hm hq
  let : IsSimpleGroup ((generalizedFitting D) ⧸ center (generalizedFitting D)) := hq.simple
  let : Nontrivial (generalizedFitting D) :=
    (QuotientGroup.mk'_surjective (center (generalizedFitting D))).nontrivial
  have hn : (generalizedFitting D).subgroupOf K ≠ ⊥ := by
    intro hn
    have he := congrArg (Subgroup.map K.subtype) hn
    rw [map_subgroupOf_eq_of_le hl, Subgroup.map_bot] at he
    exact (nontrivial_iff_ne_bot _).mp inferInstance he
  have ht := (inferInstance : ((generalizedFitting D).subgroupOf K).Normal).eq_bot_or_eq_top
  exact le_antisymm hl (subgroupOf_eq_top.mp (ht.resolve_left hn))

/-- A small subnormal subgroup in the quasisimple-component rows is that
very component, and its actual equivalence is SL₃(2) or A₅. -/
theorem fitting_eq_small (K : Subgroup D) (hK : K.IsSubnormal) (hm : SmallModel K)
    (hq : IsQuasisimple (generalizedFitting D)) :
    generalizedFitting D = K ∧
      (Nonempty (K ≃* Matrix.PSL3Two.SL) ∨ Nonempty (K ≃* alternatingGroup (Fin 5))) := by
  rcases hm with he | he | he <;> obtain ⟨e⟩ := he
  · have hl := fitting_le_small K hK (Or.inl ⟨e⟩) hq
    let := hq
    let : IsSimpleGroup ((generalizedFitting D) ⧸ center (generalizedFitting D)) := hq.simple
    let : Nontrivial (generalizedFitting D) :=
      (QuotientGroup.mk'_surjective (center (generalizedFitting D))).nontrivial
    let := symmetricThree_solvable
    let f := e.toMonoidHom.comp (inclusion hl)
    exact (Group.IsPerfect.not_isSolvable (generalizedFitting D)
      (Group.isSolvable_of_isSolvable_injective (f := f)
        (e.injective.comp (inclusion_injective hl)))).elim
  · let := simple_SL
    let : IsSimpleGroup K := e.isSimpleGroup
    exact ⟨fitting_eq_small_simple K hK (Or.inr (Or.inl ⟨e⟩)) hq, Or.inl ⟨e⟩⟩
  · let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsSimpleGroup K := e.isSimpleGroup
    exact ⟨fitting_eq_small_simple K hK (Or.inr (Or.inr ⟨e⟩)) hq, Or.inr ⟨e⟩⟩

/-- Exact component models for the subsequent F.6 row comparisons. -/
theorem fitting_small_models (K : Subgroup D) (hK : K.IsSubnormal) (hm : SmallModel K)
    (hq : IsQuasisimple (generalizedFitting D)) :
    Nonempty (generalizedFitting D ≃* Matrix.PSL3Two.SL) ∨
      Nonempty (generalizedFitting D ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨he, hm⟩ := fitting_eq_small K hK hm hq
  rcases hm with hm | hm <;> obtain ⟨e⟩ := hm
  · exact Or.inl ⟨(MulEquiv.subgroupCongr he).trans e⟩
  · exact Or.inr ⟨(MulEquiv.subgroupCongr he).trans e⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives.Nonsolvable
