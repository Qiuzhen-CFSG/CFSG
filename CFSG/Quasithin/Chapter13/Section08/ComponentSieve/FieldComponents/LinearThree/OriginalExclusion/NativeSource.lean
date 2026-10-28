module
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.Complete
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion.Application
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component
public import Theory.SpecificGroups.PSL3Two.NonSolvable
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.Overgroups.OriginalSource

/-!
# Native G.6.4 in the original binary quotient sieve

The complete known-simple G.6.4 theorem supplies the existing Chapter 13
interface, including both factor modules, normality relative to the normal
closure, the involutory extension and the central-Sylow refinement. All actor
and module markings are retained. The actual binary exclusion consumer then
uses simplicity and nonsolvability of the whole quotient to discharge the
solvable-closure branch. Only the earlier F.9 and 13.7.6 source inputs remain;
G.6.4 and the transvection model conclusion are no longer assumed. Their final discharge and the
remaining field exclusions stay with qt-d-138-fields-source.

Source: Aschbacher–Smith, G.6.4, pp.345–346; 13.8.5 and 13.8.19, pp.947,953.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion
open TransvectionRecognition TransvectionRecognition.Component.RecognitionStep
open TransvectionRecognition.Component.ModelExtension
open ChapterG.Section06
universe u
variable {A E : Type u} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
  {ρ : Representation (ZMod 2) A E} {t : A}

private theorem factor_model {K : Subgroup A} {W : Submodule (ZMod 2) E}
    (h : FactorModel ρ K W) : G64FactorAlternativeAt ρ K W := by
  rcases h with ⟨n,hn,hb,eK,eW,hs,he⟩ | ⟨n,hn,hb,eK,eW,hs,he⟩ |
    ⟨n,hn,eK,eW,hs,he⟩
  · exact ⟨hs,Or.inl ⟨n,hn,hb,eK,eW,he⟩⟩
  · exact ⟨hs,Or.inr (Or.inl ⟨n,hn,hb,eK,eW,he⟩)⟩
  · exact ⟨hs,Or.inr (Or.inr ⟨n,hn,eK,eW,he⟩)⟩

private theorem small_factor_model {K : Subgroup A} {W : Submodule (ZMod 2) E}
    (h : SmallFactorModel ρ K W) :
    G64FactorAlternativeAt ρ K W ∧ G64SmallFactor K := by
  rcases h with h | h | h
  · exact ⟨factor_model (Or.inl ⟨2,by decide,by decide,h⟩),Or.inl ⟨h.choose⟩⟩
  · exact ⟨factor_model (Or.inl ⟨3,by decide,by decide,h⟩),Or.inr (Or.inl ⟨h.choose⟩)⟩
  · exact ⟨factor_model (Or.inr (Or.inl ⟨5,by decide,by decide,h⟩)),
      Or.inr (Or.inr ⟨h.choose⟩)⟩

private theorem whole_model {B F : Type*} [Group B] [AddCommGroup F]
    [Module (ZMod 2) F] {σ : Representation (ZMod 2) B F}
    (h : HasModelOn ρ ⊤ ⊤ σ) : HasActionModel ρ σ := by
  obtain ⟨eK,eW,hs,he⟩ := h
  refine ⟨Subgroup.topEquiv.symm.trans eK,(Submodule.topEquiv).symm.trans eW,?_⟩
  intro a v
  exact he ⟨a,mem_top a⟩ ⟨v,Submodule.mem_top⟩

private theorem central_model (h : CentralModel ρ) : G64CentralAlternative ρ := by
  rcases h with ⟨n,hn,hb,hm⟩ | hm | hm | hm
  · exact Or.inl ⟨n,hn,hb,whole_model hm⟩
  · exact Or.inr (Or.inl (whole_model hm))
  · exact Or.inr (Or.inr (Or.inl (whole_model hm)))
  · exact Or.inr (Or.inr (Or.inr (whole_model hm)))

private theorem two_factors (d : TwoFactors ρ t) : Nonempty (G64SourceTwo ρ t) := by
  have h1 := small_factor_model d.first_model
  have h2 := small_factor_model d.second_model
  have hn1 : normalClosure ({t} : Set A) ≤ normalizer (d.first : Set A) := by
    rw [←d.join_eq]
    apply sup_le d.first.le_normalizer
    apply le_normalizer_iff_commutator_le_left.mpr
    rw [d.commute]
    exact bot_le
  have hn2 : normalClosure ({t} : Set A) ≤ normalizer (d.second : Set A) := by
    rw [←d.join_eq]
    apply sup_le _ d.second.le_normalizer
    apply le_normalizer_iff_commutator_le_left.mpr
    rw [commutator_comm,d.commute]
    exact bot_le
  refine ⟨{
    K1 := d.first
    K2 := d.second
    K1_le := le_sup_left.trans_eq d.join_eq
    K2_le := le_sup_right.trans_eq d.join_eq
    direct_product := d.join_eq
    trivial_intersection := d.disjoint
    commuting_factors := d.commute
    K1_normal_in_closure := ?_
    K2_normal_in_closure := ?_
    transvection_in_first := d.marked
    second_nontrivial := d.second_nontrivial
    factor_one_model := ⟨_,h1.1⟩
    factor_two_model := ⟨_,h2.1⟩
    factor_one_small := h1.2
    factor_two_small := h2.2
    extension := ?_
    module_sum := d.space_sum
    first_module := h1.1
    second_module := h2.1
    first_centralizes_second := d.cross_first
    second_centralizes_first := d.cross_second
    permutes_factors := d.permutation }⟩
  · intro x hx g hg
    exact (mem_normalizer_iff.mp (hn1 hg) x).mp hx
  · intro x hx g hg
    exact (mem_normalizer_iff.mp (hn2 hg) x).mp hx
  · obtain ⟨g,_,hg2,hggen,hg⟩ := d.extension
    have hgs : d.second.map (MulAut.conj g).toMonoidHom = d.first := by
      rcases d.permutation g with hf | hs
      · have he : d.first = d.second := hf.1.symm.trans hg
        exact (d.second_nontrivial (by simpa only [he,inf_idem] using d.disjoint)).elim
      · exact hs.2
    refine ⟨g,hg2,hggen,?_,?_⟩
    · intro x hx
      have hm := mem_map_of_mem (MulAut.conj g).toMonoidHom hx
      rw [hg] at hm
      exact hm
    · intro x hx
      have hm := mem_map_of_mem (MulAut.conj g).toMonoidHom hx
      rw [hgs] at hm
      exact hm

/-- The proved complete G.6.4 supplies all clauses of Chapter 13's universal
source interface, with the original quotient and marked factor actions. -/
theorem g64_source_knownSimple : G64SourceTheorem.{u} KnownSimple.IsKnownSimple := by
  intro A E Cover _ _ _ _ _ _ _ ρ t q hsq hq hc hf ht2 ht1 hr hg ht
  have hgen : conjugateDisplacementSpan ρ t ⊤ = displacementOrbit ρ t := by
    unfold conjugateDisplacementSpan displacementOrbit
    congr 1
    ext v
    constructor
    · rintro ⟨a,_,w,he⟩
      exact ⟨a,w,he⟩
    · rintro ⟨a,w,he⟩
      exact ⟨a,mem_top a,w,he⟩
  have h : Hypotheses KnownSimple.IsKnownSimple ρ t q := {
    finite_group := inferInstance
    finite_cover := inferInstance
    finite_displacement := inferInstance
    cover_sqtk := hsq
    quotient_surjective := hq
    twoCore := hc
    faithful := hf
    involution := ht2
    nonidentity := ht1
    displacement_rank := hr
    generated := hgen.trans hg }
  have hd := ChapterG.Section06.lemma_G_6_4 h (Component.transvection_displacement_rank ht)
  refine ⟨?_,fun P hp => ⟨(hd.2 P hp).1,central_model (hd.2 P hp).2⟩⟩
  rcases hd.1 with ho | ho
  · obtain ⟨hN,hm,hW⟩ := ho
    exact Or.inl ⟨{
      K := ⊤
      W := subspaceCommutator ρ ⊤ ⊤
      K_eq := hN.symm
      W_eq := hW
      model := factor_model hm
      whole_actor := rfl
      commutator_module := rfl }⟩
  · obtain ⟨d⟩ := ho
    exact Or.inr (two_factors d)

private theorem transvection_of_codimension_one
    {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) A E) (a : A)
    (hc : fixedCodim ρ (zpowers a) = 1) : IsTransvection ρ a := by
  let e := LinearEquiv.ofBijective (ρ a) (ρ.apply_bijective a)
  have hr : Module.finrank (ZMod 2) (LinearMap.range (e.toLinearMap - LinearMap.id)) = 1 :=
    (fixedCodim_zpowers_eq_displacement_rank ρ a).symm.trans hc
  obtain ⟨f, v, he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr hr.le
  have hformula (w : E) : ρ a w = w + f w • v :=
    congrArg (fun l : E →ₗ[ZMod 2] E => l w) he
  have hne : ρ a ≠ LinearMap.id := by
    intro hh
    have hz : e.toLinearMap - LinearMap.id = 0 := sub_eq_zero.mpr hh
    rw [hz, LinearMap.range_zero, finrank_bot] at hr
    omega
  have hf : f ≠ 0 := by
    intro hz
    apply hne
    ext w
    simpa only [hz, LinearMap.zero_apply, zero_smul, add_zero, LinearMap.id_apply] using hformula w
  have hv : v ≠ 0 := by
    intro hz
    apply hne
    ext w
    simpa only [hz, smul_zero, add_zero, LinearMap.id_apply] using hformula w
  have hfv : f v = 0 := by
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (f v) with hz | ho
    · exact hz
    have hev : e v = 0 := by
      change ρ a v = 0
      rw [hformula, ho, one_smul, ZModModule.add_self]
    exact (hv (e.map_eq_zero_iff.mp hev)).elim
  exact ⟨f, v, hf, hv, hfv, hformula⟩

variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The source transvection is an actual nonidentity involution of the whole
quotient. Only the original faithful F.9 action is used; no 13.7.6 input or
transvection-model alternative is needed. -/
theorem source_binary_involution
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : SourceAction H V₃ V₁) (e : Source.Hstar H ≃* Matrix.PSL3Two.PSL) :
    ∃ a : Source.Hstar H, a ^ 2 = 1 ∧ a ≠ 1 ∧
      fixedCodim act.representation (zpowers a) = 1 := by
  obtain ⟨a, ha⟩ := source_binary_has_transvection c act e
  have ht := transvection_of_codimension_one act.representation a ha
  have hF9 := c.f9 H c.component.local_overgroup
  have hf := SourceCompletion.f9_section_faithful _ hF9
    (SourceCompletion.Comparison.sourceSection act hF9.H_centralizes)
  exact ⟨a, Component.transvection_square hf ht, ht.ne_one, ha⟩

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- The original binary whole quotient is excluded after the genuine F.9
and 13.7.6 inputs. Its simplicity and nonsolvability discharge the solvable
normal-closure branch. The literal faithful action is constructed from the
original F.9 hypotheses. G.6.4 and transvection recognition are proved inputs;
the component quotient L₃(2) remains allowed. -/
theorem source_binary_exclusion_of_earlier
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁) :
    ¬ Nonempty (Source.Hstar H ≃* Matrix.PSL3Two.PSL) := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) :=
    c.localSetup.uh_elementary c.component.local_overgroup
  have hF9 := c.f9 H c.component.local_overgroup
  let act := SourceCompletion.Comparison.conjugationAction
    (c.localSetup.line_le_uh H) hF9.plus_le_H
    (hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    hF9.commutator_UH_QH_le_point
  rintro ⟨e⟩
  obtain ⟨a,ha⟩ := source_binary_has_transvection c act e
  have ht := transvection_of_codimension_one act.representation a ha
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.Comparisons.Exceptional.psl3Two_simple
  let : IsSimpleGroup (Source.Hstar H) := e.isSimpleGroup
  have hn : normalClosure ({a} : Set (Source.Hstar H)) = ⊤ := by
    apply (inferInstance : (normalClosure ({a} : Set (Source.Hstar H))).Normal).eq_bot_or_eq_top.resolve_left
    intro he
    have hm : a ∈ normalClosure ({a} : Set (Source.Hstar H)) :=
      subset_normalClosure (Set.mem_singleton a)
    rw [he] at hm
    exact ht.ne_one hm
  have hns : ¬ Group.IsSolvable (normalClosure ({a} : Set (Source.Hstar H))) := by
    rw [hn]
    intro hsol
    let := hsol
    let : Group.IsSolvable (Source.Hstar H) :=
      Group.isSolvable_of_surjective (f := (Subgroup.topEquiv :
        (⊤ : Subgroup (Source.Hstar H)) ≃* Source.Hstar H).toMonoidHom)
        Subgroup.topEquiv.surjective
    exact not_isSolvable_psl3_two
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  obtain ⟨_,hm⟩ := Component.complete_conclusions_of_nonsolvable_closure T
    c.localSetup earlier g64_source_knownSimple c.component.local_overgroup
    act.representation act.conjugation a ht hns
  apply (source_binary_exclusion_of_transvection_models c act (fun _ => ?_)) ⟨e⟩
  rcases hm with ⟨hm,_,_⟩ | ⟨hm,_⟩
  · rcases hm with ⟨e6,_⟩ | ⟨⟨e6,_⟩,_⟩ <;> exact Or.inl ⟨e6⟩
  · rcases hm with ⟨e7,_⟩ | ⟨e4,_⟩
    · exact Or.inr (Or.inl ⟨e7⟩)
    · exact Or.inr (Or.inr ⟨e4⟩)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OriginalExclusion

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.Overgroups
universe u
open Theory.GroupTheory
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open TransvectionRecognition.Component.ModelExtension
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9 : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
  (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
  (fields : ∀ {J C : Subgroup G}, SourceContext T L V V₁ V₂ V₃ M G₁ J C →
    ¬ HigherFieldAlternative (C ⧸ pCore 2 C))
include d h hF9 hcentral hcomm earlier fields

/-- Apply the native binary exclusion to unrestricted original overgroups.
The remaining field exclusion and genuine earlier 13.7.6 inputs stay explicit;
no binary exclusion or transvection classifier is assumed. -/
theorem original_component_conclusions_of_earlier :
    AlternatingAndLinear.LinearReduction.OriginalSource.ComponentConclusions
      (one L T V₁) T G₁ M :=
  original_component_conclusions d h hF9 hcentral hcomm fields
    (fun c => LinearThree.OriginalExclusion.source_binary_exclusion_of_earlier c earlier)

/-- The same source proof supplies the actual linear-sieve group facts,
including its binary automorphism clause, with earlier premises retained. -/
theorem original_linear_group_facts_of_earlier :
    AlternatingAndLinear.LinearReduction.SourceReduction.GroupFacts
      L (one L T V₁) T V V₁ V₃ G₁ M :=
  original_linear_group_facts d h hF9 hcentral hcomm fields
    (fun c => LinearThree.OriginalExclusion.source_binary_exclusion_of_earlier c earlier)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.Overgroups
