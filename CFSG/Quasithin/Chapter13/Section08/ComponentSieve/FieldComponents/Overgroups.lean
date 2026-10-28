module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.Overgroups.ModelFacts
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource.SixComplete
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource.Groups
public import Theory.GroupTheory.CComponent.UniqueResidual
public import Theory.GroupTheory.PGroup.CriticalSubgroup

/-!
# Extending the field sieve to arbitrary source overgroups

Restrict each relative component to KL₁T and apply the checked containment
and quotient sieve there. The earlier Fitting alternatives then place F(H*)
inside a centerless component, so F(H*) is trivial. Distinct components of
the resulting radical-free quotient commute; they cannot both contain the
nontrivial image of L₁. Thus the component is unique. Its outer two-group
makes the actual Sylow subgroup a supplement, giving the set product H=KT.
The seed commutator identity also gives U_H=[U_H,K] for the original H.

The final application constructs the ComponentConclusions used by the
binary parabolic reduction. Higher-field exclusion and the separate
whole-quotient L₃(2) exclusion remain explicit and belong to
qt-d-138-fields-source. The context contains only the original setup and
earlier 13.8.16–17 normality and catalogue; its source construction is in
Overgroups/OriginalSource. The original setup producers and final source
discharge remain with qt-d-1381-source.
Source: Aschbacher–Smith, 13.8.21(1–4), printed pp.955–957, especially the
last paragraph of its proof; relative component restriction is A.3.3(2).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.Overgroups
open LinearThree.Geometry.ExternalComponentAction LinearThree.Geometry.ParabolicMarking
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open SourceCompletion TransvectionRecognition.Component.ModelExtension

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- Earlier inputs for an arbitrary member of Hz. The two component fields
are exactly preceding 13.8.16–17; no generated-overgroup or field-sieve
conclusion is assumed. -/
structure Context (T : Sylow 2 G) (L V V₁ V₂ V₃ M G₁ H : Subgroup G) where
  localSetup : LocalSetup T L V V₁ V₂ V₃ M G₁
  maximal : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L
  f9 : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis
  centralizer : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G)
  noncentral_core : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥
  earlier1339 : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁
  sqtk : IsSQTK KnownSimple.IsKnownSimple H
  member : H ∈ Source.Hz (one L T V₁) T G₁ M
  normal : ∀ K : Subgroup G, K ≤ H → (K.subgroupOf H).IsCComponent → (K.subgroupOf H).Normal
  catalogue : ∀ K : Subgroup G, K ≤ H → (K.subgroupOf H).IsCComponent →
    Components.Models.ComponentModel (K ⧸ pCore 2 K)

variable (c : Context T L V V₁ V₂ V₃ M G₁ H)

/-- Construct the original source context on KL₁T, with the same component
and all literal local flags, cores and quotients. -/
def reducedContext (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    SourceContext T L V V₁ V₂ V₃ M G₁ (K ⊔ one L T V₁ ⊔ (T : Subgroup G)) K := by
  let J := K ⊔ one L T V₁ ⊔ (T : Subgroup G)
  have hJH : J ≤ H := sup_le (sup_le hKH (le_sup_left.trans c.member.1.2))
    (le_sup_right.trans c.member.1.2)
  have hKJ : K ≤ J := le_sup_left.trans le_sup_left
  have hex := SolvableSource.solvable_overgroup_source c.localSetup c.maximal c.f9
    c.centralizer c.noncentral_core c.earlier1339
  obtain ⟨hout,hmem,_⟩ := LocalFitting.source_component c.localSetup c.member c.earlier1339 hex K hKH hK
  have hJ : J ∈ Source.Hz (one L T V₁) T G₁ M := by
    simpa only [J, sup_assoc, sup_comm (T : Subgroup G) (one L T V₁)] using hmem
  exact {
    localSetup := c.localSetup
    maximal := c.maximal
    f9 := c.f9
    centralizer := c.centralizer
    noncentral_core := c.noncentral_core
    earlier1339 := c.earlier1339
    component := {
      sqtk := (IsSQTK.equiv (subgroupOfEquivOfLe hJH)).mp
        (c.sqtk.subgroup (J.subgroupOf H))
      local_overgroup := hJ
      generated := rfl
      component := hK.subgroupOf_of_le hKJ hJH
      normal := (normal_subgroupOf_iff_le_normalizer hKJ).mpr
        (hJH.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp (c.normal K hKH hK)))
      external := hout
      theta := (Section07.ModelExclusions.theta_intersection (localNaturalSetup c.localSetup) c.maximal hJ).symm }
    catalogue := c.catalogue K hKH hK }

variable (hfield : ∀ K : Subgroup G, K ≤ H → (K.subgroupOf H).IsCComponent →
  ¬ HigherFieldAlternative (K ⧸ pCore 2 K))

include c hfield

/-- Containment and the remaining quotient list pass from KL₁T to the
original overgroup. All three small-cover rows are discharged. -/
theorem containment_and_models (K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) :
    one L T V₁ ≤ K ∧ RemainingQuotient (K ⧸ pCore 2 K) := by
  have h := SmallCovers.OriginalSource.source_consequences_of_field_exclusion
    (reducedContext c K hKH hK) (hfield K hKH hK)
  exact ⟨h.1,h.2.1⟩

/-- The source residual alternatives put F(H*) inside K*, whose center is trivial. -/
theorem fitting_eq_bot (K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) : fittingSubgroup (Source.Hstar H) = ⊥ := by
  obtain ⟨hLK,hm⟩ := containment_and_models c hfield K hKH hK
  have hex := SolvableSource.solvable_overgroup_source c.localSetup c.maximal c.f9
    c.centralizer c.noncentral_core c.earlier1339
  have hr := Components.Fitting.fitting_star_alternatives H L (one L T V₁) (plus L T V₁)
    (LocalFitting.whole_residual c.localSetup c.member c.earlier1339 hex)
  have hfK : fittingSubgroup (Source.Hstar H) ≤ Source.starImage H K := by
    rcases hr with hb | ⟨_,he⟩ | ⟨_,he⟩
    · rw [hb]; exact bot_le
    · rw [he]; exact starImage_mono H hLK
    · rw [he]; exact starImage_mono H ((plus_le_one L T V₁ c.localSetup.line_stable).trans hLK)
  have hfc := (LocalFitting.component_fitting c.localSetup c.member c.earlier1339 hex K hK).1
  have hz : center (Source.starImage H K) = ⊥ := (remaining_model_facts_of_equiv
    (Components.componentStarEquiv H K hKH hK).symm hm).1
  have hb : Source.starImage H K ⊓ centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊥ := by
    rw [← map_center_subtype_eq_inf_centralizer, hz, Subgroup.map_bot]
  exact le_bot_iff.mp ((le_inf hfK hfc).trans hb.le)

/-- No two distinct components can both contain the nontrivial source seed actor. -/
theorem unique_component (K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) :
    ∀ D : Subgroup H, D.IsCComponent → D = K.subgroupOf H := by
  have hf := fitting_eq_bot c hfield K hKH hK
  have hr := radical_bot_of_fitting_bot hf
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  have hn : ¬ one L T V₁ ≤ Source.QH H := by
    intro hh
    have hseed := Section07.ModelExclusions.seed_commutator_point_residual (localNaturalSetup c.localSetup)
    have hle : V₃ ≤ V₁ := hseed.symm.le.trans
      ((commutator_mono (le_conjugateSpanBy V₃ H) hh).trans
        (c.f9 H c.member).commutator_UH_QH_le_point)
    exact not_le_of_gt (c.f9 H c.member).point_lt hle
  have hsne : Source.starImage H (one L T V₁) ≠ ⊥ := by
    intro he
    apply hn
    intro x hx
    have hLH : one L T V₁ ≤ H := le_sup_left.trans c.member.1.2
    let y : H := ⟨x, hLH hx⟩
    have hy : QuotientGroup.mk' (pCore 2 H) y ∈ Source.starImage H (one L T V₁) := ⟨y,hx,rfl⟩
    rw [he,mem_bot] at hy
    exact ⟨y,(QuotientGroup.eq_one_iff y).mp hy,rfl⟩
  intro D hD
  let B := D.map H.subtype
  have hBH : B ≤ H := map_subtype_le _
  have hBD : B.subgroupOf H = D := comap_map_eq_self_of_injective H.subtype_injective D
  have hB : (B.subgroupOf H).IsCComponent := hBD ▸ hD
  have hLB := (containment_and_models c hfield B hBH hB).1
  have hLK := (containment_and_models c hfield K hKH hK).1
  let q := QuotientGroup.mk' (pCore 2 H)
  have he : D.map q = (K.subgroupOf H).map q := by
    by_contra hne
    have hcomm := (hD.map_quotient (pCore 2 H)).commutator_eq_bot_of_ne_of_solvableRadical_eq_bot
      hr (hK.map_quotient _) hne
    have hz : center (Source.starImage H K) = ⊥ := (remaining_model_facts_of_equiv
      (Components.componentStarEquiv H K hKH hK).symm
      (containment_and_models c hfield K hKH hK).2).1
    have hb : Source.starImage H K ⊓ centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊥ := by
      rw [← map_center_subtype_eq_inf_centralizer, hz, Subgroup.map_bot]
    apply hsne
    apply le_bot_iff.mp
    apply le_trans (le_inf (starImage_mono H hLK) ?_) hb.le
    have hc : Source.starImage H B ≤ centralizer (Source.starImage H K : Set (Source.Hstar H)) := by
      rw [← commutator_eq_bot_iff_le_centralizer]
      simpa only [Source.starImage,hBD] using hcomm
    exact (starImage_mono H hLB).trans hc
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  exact hD.eq_of_map_quotient_eq hK (pCore 2 H) he

/-- The source outer two-group bound supplies the full set product H=KT,
not just the product inside the reduced overgroup. -/
theorem product (K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) :
    (H : Set G) = (K : Set G) * (T : Set G) := by
  have hu := unique_component c hfield K hKH hK
  have hf := fitting_eq_bot c hfield K hKH hK
  have hm := (containment_and_models c hfield K hKH hK).2
  let e := QuotientGroup.congr (pCore 2 (K.subgroupOf H)) (pCore 2 K)
    (subgroupOfEquivOfLe hKH) (pCore_map_iso 2 _)
  have ho := (remaining_model_facts_of_equiv e hm).2
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans c.member.1.2
  have hh := hK.sylow_sup_eq_top_of_outer_twoGroup hu hf ho (T.subtype hTH)
  have hjoin : K ⊔ (T : Subgroup G) = H := by
    have he := congrArg (map H.subtype) hh
    simpa only [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hKH,
      map_subgroupOf_eq_of_le hTH,← MonoidHom.range_eq_map,range_subtype] using he
  rw [← hjoin]
  exact (coe_mul_of_right_le_normalizer_left K (T : Subgroup G)
    (hTH.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp (c.normal K hKH hK))))

/-- The same set product, expressed as a subgroup join for the source action. -/
theorem join_eq (K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) : K ⊔ (T : Subgroup G) = H := by
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans c.member.1.2
  apply SetLike.coe_injective
  exact (coe_mul_of_right_le_normalizer_left K (T : Subgroup G)
    (hTH.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp (c.normal K hKH hK)))).trans
      (product c hfield K hKH hK).symm

/-- The original U_H is generated by the component, including when H was
not initially assumed to be KL₁T. -/
theorem commutator_eq (K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) :
    Source.UH H V₃ = ⁅Source.UH H V₃,K⁆ := by
  exact (Section07.ModelExclusions.component_normal_and_span_of_one_le
    (localNaturalSetup c.localSetup) c.member (c.f9 H c.member) hKH hK
    (containment_and_models c hfield K hKH hK).1).2.symm

/-- The full overgroup now satisfies the original reduced source interface;
its generation field is proved by the unique-component and outer-action argument. -/
def originalContext (K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) : SourceContext T L V V₁ V₂ V₃ M G₁ H K := by
  have he : K ⊔ one L T V₁ ⊔ (T : Subgroup G) = H := by
    rw [sup_eq_left.mpr (containment_and_models c hfield K hKH hK).1]
    exact join_eq c hfield K hKH hK
  exact he ▸ reducedContext c K hKH hK

/-- The binary automorphism conclusion for the full overgroup. Only the
separate whole-quotient exclusion from 13.8.19 is still required. -/
theorem binary_automorphism (K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.PSL)
    (hnot : ¬ Nonempty (Source.Hstar H ≃* Matrix.PSL3Two.PSL)) :
    Nonempty (Source.Hstar H ≃* MulAut Matrix.PSL3Two.PSL) :=
  source_binary_automorphism (originalContext c hfield K hKH hK) eK hnot

omit c hfield in
/-- Assemble the literal preceding 13.8.21 input consumed by the later linear
sieve. The earlier component source produces contexts; this field owner retains
both uniform field exclusion and whole-quotient binary exclusion. -/
theorem component_conclusions
    (contexts : ∀ J : Subgroup G, J ∈ Source.Hz (one L T V₁) T G₁ M →
      Nonempty (Context T L V V₁ V₂ V₃ M G₁ J))
    (fields : ∀ {J C : Subgroup G}, SourceContext T L V V₁ V₂ V₃ M G₁ J C →
      ¬ HigherFieldAlternative (C ⧸ pCore 2 C))
    (binary : ∀ {J C : Subgroup G}, SourceContext T L V V₁ V₂ V₃ M G₁ J C →
      ¬ Nonempty (Source.Hstar J ≃* Matrix.PSL3Two.PSL)) :
    AlternatingAndLinear.LinearReduction.OriginalSource.ComponentConclusions (one L T V₁) T G₁ M := by
  have hf (J : Subgroup G) (a : Context T L V V₁ V₂ V₃ M G₁ J)
      (C : Subgroup G) (hCJ : C ≤ J) (hC : (C.subgroupOf J).IsCComponent) :=
    fields (reducedContext a C hCJ hC)
  refine {
    base_le := ?_
    models := ?_
    product := ?_
    three_automorphisms := ?_ }
  · intro J C hJ hCJ hC
    obtain ⟨a⟩ := contexts J hJ
    exact (containment_and_models a (hf J a) C hCJ hC).1
  · intro J C hJ hCJ hC
    obtain ⟨a⟩ := contexts J hJ
    exact (containment_and_models a (hf J a) C hCJ hC).2
  · intro J C hJ hCJ hC
    obtain ⟨a⟩ := contexts J hJ
    exact product a (hf J a) C hCJ hC
  · intro J C hJ hCJ hC he
    obtain ⟨a⟩ := contexts J hJ
    obtain ⟨e⟩ := he
    exact binary_automorphism a (hf J a) C hCJ hC e
      (binary (originalContext a (hf J a) C hCJ hC))

omit c hfield in
/-- Actual downstream application: every group premise of the binary
parabolic reduction follows, retaining precisely the two unproved exclusions
and their independent preceding source producers. -/
theorem linear_group_facts
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hF9 : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
      (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
    (contexts : ∀ J : Subgroup G, J ∈ Source.Hz (one L T V₁) T G₁ M →
      Nonempty (Context T L V V₁ V₂ V₃ M G₁ J))
    (fields : ∀ {J C : Subgroup G}, SourceContext T L V V₁ V₂ V₃ M G₁ J C →
      ¬ HigherFieldAlternative (C ⧸ pCore 2 C))
    (binary : ∀ {J C : Subgroup G}, SourceContext T L V V₁ V₂ V₃ M G₁ J C →
      ¬ Nonempty (Source.Hstar J ≃* Matrix.PSL3Two.PSL)) :
    AlternatingAndLinear.LinearReduction.SourceReduction.GroupFacts L (one L T V₁) T V V₁ V₃ G₁ M :=
  AlternatingAndLinear.LinearReduction.OriginalSource.group_facts d h hF9 hcentral hcomm hsource
    (component_conclusions contexts fields binary)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.Overgroups
