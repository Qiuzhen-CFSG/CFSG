module
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.RankOneExclusions
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage.Structure
public import Theory.Representation.BinaryOffender.QuadraticComponentSection
public import Theory.Representation.BinaryOffender.GeneratedCore

/-!
# Quadratic actors exclude the projective unitary-eight component

Restrict the actual binary representation to the component and its quadratic
actor. An irreducible section detects the simple component and retains the
quadratic displacement bound. Its kernel centralizes the component, so the
whole actor remains faithful. The resulting faithful action image has that
same PSU₃(8) component as its generalized Fitting subgroup and inherits SQTK.
Native unitary recognition, including the proved scalar covering theorem,
forces its center to have order three, contradicting projectivity.

No constituent choice, natural-module identification, containment of L₁,
or vanishing component-central complement is assumed. The original-source
application is HigherFieldReduction/OriginalSource/ProjectiveUnitary.
Source: Aschbacher–Smith, 13.8.20, printed p.955, using F.9.18(2–4),
B.4.5 and K.3.3, printed pp.325–326,87,456.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.UnitaryEight.Projective
open HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.ActionImage
universe u
variable {D W : Type u} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W]

section Recognition
variable {X U : Type u} [Group X] [Finite X] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

/-- The actual projective unitary model is quasisimple and centerless. -/
theorem model_facts {C : Type*} [Group C]
    (hm : ClassicalGroup.IsPSU C 3 8) :
    IsQuasisimple C ∧ center C = ⊥ ∧ ClassicalGroup.IsPSU (C ⧸ center C) 3 8 := by
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hm
  have hfixed := BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.card_fixed J hcard hconj
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    BenderSuzuki.External.huppert_II_10_13 J 8 (by decide) hcard hfixed
  let := J.projective_isQuasisimple_of_fixed_card (by decide : 2 < 8) hcard hfixed
  have hzP : center (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ :=
by
    rcases (inferInstance : (center
        (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)).Normal).eq_bot_or_eq_top
        with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp h)).elim
  have hz : center C = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [Nat.card_congr (centerCongr e).toEquiv,hzP,Subgroup.card_bot]
  refine ⟨IsQuasisimple.of_mulEquiv e.symm,hz,F,inferInstance,inferInstance,J,hcard,hconj,⟨?_⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans e

/-- Native unitary recognition forces a center of order three, excluding
PSU₃(8) at quadratic ratio at most two. -/
theorem quadraticRatio_gt_two
    (ρ : Representation (ZMod 2) X U) (K : Subgroup X)
    (hsq : IsSQTK KnownSimple.IsKnownSimple X) (hfit : generalizedFitting X = K)
    (hm : ClassicalGroup.IsPSU K 3 8) (hf : Function.Injective ρ)
    (hi : IsIrreducible (ρ.comp K.subtype)) : 2 < quadraticRatio ρ := by
  classical
  by_contra hn
  have hsmall : quadraticRatio ρ ≤ 2 := le_of_not_gt hn
  obtain ⟨hqs,hz,hquot⟩ := model_facts hm
  have h : ChapterK.RankOne.SourceHypotheses ρ K :=
    ⟨hsq,hfit,hqs,hf,hi,(cubicRatio_le_quadraticRatio ρ).trans hsmall⟩
  have hc := (h.unitary_case_of_cover_lifting (s := 3) (by decide) hquot
    (fun F _ _ J hcard hconj e => ChapterB.SourceClassification.unitary_central_quotient
      h J (by decide) hcard hconj e) (Classical.choice (inferInstance : Nonempty (Sylow 2 X)))).2.1
  rw [hz,Subgroup.card_bot] at hc
  norm_num at hc
end Recognition

/-- Exclude a component-faithful quadratic supplement on the actual section. -/
theorem no_quadratic_supplement
    (ρ : Representation (ZMod 2) D W) (K A : Subgroup D) [K.Normal]
    (hsq : IsSQTK KnownSimple.IsKnownSimple D) (hm : ClassicalGroup.IsPSU K 3 8)
    (hgen : K ⊔ A = ⊤) (hA : IsElementaryTwo A)
    (hq : IsQuadratic ρ A) (hd : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : A ⊓ centralizer (K : Set D) = ⊥) (hn : ¬ K ≤ ρ.ker) : False := by
  obtain ⟨hqs,hz,_⟩ := model_facts hm
  let : IsQuasisimple K := hqs
  let : IsSimpleGroup (K ⧸ center K) := hqs.simple
  let : IsSimpleGroup K :=
    (((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm).isSimpleGroup
  obtain ⟨U,N,hi,hnN,hqN,hdN⟩ :=
    exists_component_irreducible_quadratic_section ρ K A hz hgen hA hq hd hAC hn
  let σ := N.quotientRepresentation
  let : Finite (U ⧸ N.toSubmodule) := Finite.of_surjective _ N.toSubmodule.mkQ_surjective
  have hsurvive : ¬ K ≤ (actionHom σ).ker := by
    intro hk
    apply hnN
    intro k hkK
    exact LinearMap.ext ((actionHom_eq_one_iff σ k).mp (hk hkK))
  have hquot : IsPGroup 2 (D ⧸ K) :=
    quotient_isPGroup_of_sup_eq_top A K hA.2.isPGroup ((sup_comm A K).trans hgen)
  obtain ⟨_,hi',hfit⟩ := Structure.image_structure σ K hsurvive hquot hi
  have hsq' := Structure.image_sqtk σ K hsurvive hsq hquot hz
  let e := Structure.componentEquiv σ K hsurvive hz
  have hfA : ∀ a ∈ A, (∀ v, σ a v = v) → a = 1 := by
    have hk := (show IsComponent D K from
      ⟨(inferInstance : K.Normal).isSubnormal,hqs⟩).normal_dichotomy (actionHom σ).ker
    have hc := commutator_eq_bot_iff_le_centralizer.mp
      ((commutator_comm _ _).trans (hk.resolve_left hsurvive))
    intro a ha hfix
    exact mem_bot.mp (hAC ▸ (show a ∈ A ⊓ centralizer (K : Set D) from
      ⟨ha,hc ((actionHom_eq_one_iff σ a).mpr hfix)⟩))
  have hsmall : quadraticRatio (imageRepresentation σ) ≤ 2 := by
    apply (quadraticRatio_le_two_iff _).mpr
    refine ⟨actionSubgroup σ A,hA.actionSubgroup σ hfA,?_,?_⟩
    · rintro a ⟨x,hx,rfl⟩ b ⟨y,hy,rfl⟩ v
      exact hqN x hx y hy v
    · rw [fixedCodim_actionSubgroup,actionSubgroup_rank σ A hfA]
      exact hdN
  exact not_le_of_gt
    (quadraticRatio_gt_two (imageRepresentation σ) (actionSubgroup σ K) hsq' hfit
      (hm.of_mulEquiv e.symm) (imageRepresentation_injective σ) hi') hsmall
/-- A normal PSU₃(8) component cannot admit a quadratic actor of ratio at
most two faithful on that component, even with a nontrivial centralizer. -/
theorem no_quadratic_actor
    (ρ : Representation (ZMod 2) D W) (K A : Subgroup D) [K.Normal]
    (hsq : IsSQTK KnownSimple.IsKnownSimple D) (hm : ClassicalGroup.IsPSU K 3 8)
    (hf : Function.Injective ρ) (hA : IsElementaryTwo A)
    (hq : IsQuadratic ρ A) (hd : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : A ⊓ centralizer (K : Set D) = ⊥) : False := by
  let E := K ⊔ A
  let K₀ := K.subgroupOf E
  let A₀ := A.subgroupOf E
  let σ := ρ.comp E.subtype
  let eK : K₀ ≃* K := subgroupOfEquivOfLe le_sup_left
  let : IsElementaryAbelian 2 A := hA.2
  have hA₀ : IsElementaryTwo A₀ := by
    refine ⟨?_,IsElementaryAbelian.subgroupOf (show A ≤ E from le_sup_right)⟩
    intro he
    change A.subgroupOf E = ⊥ at he
    exact hA.1 (by
      rw [←map_subgroupOf_eq_of_le (show A ≤ E from le_sup_right),he,Subgroup.map_bot])
  have hq₀ : IsQuadratic σ A₀ := fun a ha b hb v => hq a ha b hb v
  have hd₀ : fixedCodim σ A₀ ≤ 2 * rank A₀ := by
    rw [fixedCodim_subgroupOf ρ (show A ≤ E from le_sup_right),
      rank_subgroupOf (show A ≤ E from le_sup_right)]
    exact hd
  have hgen : K₀ ⊔ A₀ = ⊤ := by
    rw [←subgroupOf_sup (show K ≤ E from le_sup_left) (show A ≤ E from le_sup_right)]
    exact subgroupOf_self _
  have hAC₀ : A₀ ⊓ centralizer (K₀ : Set E) = ⊥ := by
    apply bot_unique
    rintro a ⟨ha,hc⟩
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hAC]
    refine ⟨ha,mem_centralizer_iff.mpr (fun k hk => ?_)⟩
    exact congrArg Subtype.val (mem_centralizer_iff.mp hc
      (⟨k,show k ∈ E from mem_sup_left hk⟩ : E) hk)
  have hm₀ := hm.of_mulEquiv eK
  have hn : ¬ K₀ ≤ σ.ker := by
    intro hk
    have hb : K₀ = ⊥ := bot_unique (hk.trans
      ((MonoidHom.ker_eq_bot_iff σ).mpr (hf.comp E.subtype_injective)).le)
    let := (model_facts hm₀).1
    let : IsSimpleGroup (K₀ ⧸ center K₀) := IsQuasisimple.simple
    let : Nontrivial K₀ := (QuotientGroup.mk'_surjective (center K₀)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot K₀).mp inferInstance hb
  exact no_quadratic_supplement σ K₀ A₀ (hsq.subgroup E) hm₀ hgen hA₀ hq₀ hd₀ hAC₀ hn

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.UnitaryEight.Projective
