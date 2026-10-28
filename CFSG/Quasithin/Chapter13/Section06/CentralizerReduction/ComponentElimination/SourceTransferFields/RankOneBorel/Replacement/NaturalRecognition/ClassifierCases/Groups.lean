module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.ClassifierCases.Models
public import Theory.GroupTheory.GeneralizedFitting.ComponentProductProjection
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.SpecificGroups.Alternating.TwoThreeCycles

/-!
# The genuine group branches for a rank-one component

Component maximality identifies the marked component with F*(D) in the
quasisimple branch. Perfectness excludes the solvable S₃ case. For the adequate
outer A₆–C₃ shape, the displayed product is normal with cyclic quotient, so
it contains the perfect component. Projection to A₆ and component simplicity
force an actual A₆ isomorphism, contradicting its three-rank.

This leaves every module clause in B.5.1 and the two product alternatives
B.5.6(3),(5) intact. It makes no use of the disputed outer-space splitting.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, pp.99–105, 931.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.ClassifierCases
open ChapterB.QuasisimpleSource ChapterB.SourceInduction

open CFSG.Quasithin.ChapterB
open scoped IsMulCommutative
variable {D : Type*} [Group D] [Finite D] {C : Subgroup D}

/-- A normal quasisimple subgroup equals a quasisimple generalized Fitting subgroup. -/
theorem component_eq_fitting [C.Normal] (hc : IsQuasisimple C)
    (hf : IsQuasisimple (generalizedFitting D)) : C = generalizedFitting D := by
  have hC : IsComponent D C := ⟨(inferInstance : C.Normal).isSubnormal, hc⟩
  exact hC.eq_of_le ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal, hf⟩
    (component_le_generalizedFitting D C hC)

omit [Finite D] in
private theorem normalizes_of_automorphism (S : Subgroup D) (t : D)
    (α : MulAut S) (hα : ∀ a : S, (α a : D) = t * a * t⁻¹) :
    t ∈ normalizer (S : Set D) := by
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx
    rw [← hα ⟨x, hx⟩]
    exact (α ⟨x, hx⟩).property
  · intro hx
    let y : S := ⟨t * x * t⁻¹, hx⟩
    have he := hα (α.symm y)
    rw [α.apply_symm_apply] at he
    have hx' : x = (α.symm y : D) := (MulAut.conj t).injective he
    rw [hx']
    exact (α.symm y).property

/-- Perfectness puts the component in the displayed normal product. Its
projection away from C₃ is an actual component of A₆, hence all of A₆.
This contradicts the three-rank bound; no module splitting is used. -/
theorem no_outerSixThree [C.Normal] (hc : IsQuasisimple C)
    (F : BinaryField) (e : C ≃* SL(2,F.Carrier)) (c : OuterSixThreeShape D) : False := by
  let : IsQuasisimple C := hc
  let P := c.first ⊔ c.second
  let : P.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← c.generates]
    refine sup_le P.le_normalizer (zpowers_le.mpr ?_)
    obtain ⟨a, ha, _⟩ := c.firstOuter
    obtain ⟨b, hb, _⟩ := c.secondOuter
    exact normalizer_inf_normalizer_le_normalizer_sup _ _
      ⟨normalizes_of_automorphism _ _ a ha, normalizes_of_automorphism _ _ b hb⟩
  let : IsCyclic (D ⧸ P) := by
    let q := QuotientGroup.mk' P
    apply isCyclic_iff_exists_zpowers_eq_top.mpr
    refine ⟨q c.element, ?_⟩
    have h := congrArg (Subgroup.map q) c.generates
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
      MonoidHom.map_zpowers, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
    exact h
  have hCP : C ≤ P := le_of_isPerfect_of_solvable_quotient C P
  have hC : IsComponent D C := ⟨(inferInstance : C.Normal).isSubnormal, hc⟩
  let t : P ≃* c.second × c.first := c.product.symm.trans MulEquiv.prodComm
  let J := (C.subgroupOf P).map t.toMonoidHom
  have hJ : IsComponent (c.second × c.first) J := (hC.subgroupOf hCP).map_equiv t
  let : Group.IsSolvable c.second := Group.isSolvable_of_isSolvable_injective
    (f := c.secondEquiv.toMonoidHom) c.secondEquiv.injective
  obtain ⟨A, hA, ⟨ea⟩⟩ := hJ.equiv_component_of_solvable_prod J
  let ec : C ≃* A := ((subgroupOfEquivOfLe hCP).symm.trans
    (t.subgroupMap (C.subgroupOf P))).trans ea
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup c.first := c.firstEquiv.isSimpleGroup_congr.mpr inferInstance
  have hat : A = ⊤ := by
    rcases hA.1.eq_bot_or_top_of_isSimpleGroup (inferInstance : IsSimpleGroup c.first) with ha | ha
    · let : IsQuasisimple A := hA.2
      let : IsSimpleGroup (A ⧸ center A) := IsQuasisimple.simple
      let : Nontrivial A := (QuotientGroup.mk'_surjective (center A)).nontrivial
      exact ((Subgroup.nontrivial_iff_ne_bot A).mp inferInstance ha).elim
    · exact ha
  let eca : C ≃* alternatingGroup (Fin 6) := ec.trans
    (((MulEquiv.subgroupCongr hat).trans Subgroup.topEquiv).trans c.firstEquiv)
  have hr : primeRank 3 C ≤ 1 := (primeRank_equiv 3 e).trans_le (three_rank_le F)
  rw [primeRank_equiv 3 eca] at hr
  have hh := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 6) (by decide)
  omega

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V}

/-- The full adequate classification leaves precisely its three module branches. -/
theorem source_cases [C.Normal] (hc : IsQuasisimple C)
    (F : BinaryField) (e : C ≃* SL(2,F.Carrier))
    (h : AdequateAlternative ρ) :
    Nonempty (ProjectiveLine.QuasisimpleSourceConclusion ρ C) ∨
      Nonempty (SourceTwoFactorCase ρ) ∨ Nonempty (HyperplaneCase ρ) := by
  let : IsQuasisimple C := hc
  let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
  let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
  let : Nontrivial D := Function.Injective.nontrivial C.subtype_injective
  cases h.of_nontrivial ρ with
  | quasisimple hf c =>
    left
    rw [component_eq_fitting hc hf]
    exact ⟨c⟩
  | symmetricThree c =>
    let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
      apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
    let : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective
      (f := c.equiv.toMonoidHom.comp C.subtype) (c.equiv.injective.comp C.subtype_injective)
    exact (Group.IsPerfect.not_isSolvable C inferInstance).elim
  | twoFactors c => exact Or.inr (Or.inl ⟨c⟩)
  | outerSixThree c => exact (no_outerSixThree hc F e c).elim
  | hyperplane c => exact Or.inr (Or.inr ⟨c⟩)
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.ClassifierCases
end
