module
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SourceResidualModule
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.Conclusions
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Stellmacher.CentralizerQuotientRepresentation
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.Replacement

/-!
# Thompson generation and the genuine unique-factor qrc alternative

In the centralizing-Q branch, J(R) cannot lie in R₂: heredity would make
it normal in both original groups. The actual minimal-parabolic theorem
therefore gives O²(G₂)=[O²(G₂),J(R)]. Its action on the reduced residual
module I is nontrivial; B.2.7 constructs an offender on the original
faithful conjugation image, so I is the required reduced FF witness.

If the first module is not FF, B.2.7 also gives J(T)=J(R), completing all
StructuralConclusion fields. Hence the unique-chief-factor branch of
D.1.5 has exactly its original alternatives (2), (3), or (5), without any
extra source premise. This does not assert the standalone D.1.4 dichotomy
in the first-module-FF case or the later A₃-block addendum.
Source: Aschbacher–Smith, D.1.4–5, printed pp.176–177.
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.UniqueFactor
variable {G : Type*} [Group G] {G₁ G₂ T V : Subgroup G}
theorem source_thompson_core_not_le_right_core
    (d : QRCConfiguration G₁ G₂ T V) (hne : V ≠ ⊥)
    (hc : intersectionClosure G₁ G₂ ≤ centralizer (V : Set G)) :
    ¬ elementaryAbelianMaxJ (twoCoreIn G₁) ≤ twoCoreIn G₂ := by
  let := d.finite_left
  let R := twoCoreIn G₁
  let Q := R ⊓ twoCoreIn G₂
  let : Finite R := Finite.of_injective (inclusion (twoCore_le G₁))
    (inclusion_injective (twoCore_le G₁))
  have hJR : elementaryAbelianMaxJ R ≤ R := sSup_le fun _ hA => hA.1
  have hRne : R ≠ ⊥ := fun he => hne (bot_unique (d.module_le_core.trans he.le))
  intro hJ₂
  have hJQ : elementaryAbelianMaxJ Q = elementaryAbelianMaxJ R :=
    elementaryAbelianMaxJ_eq_of_intermediate_finite R Q (le_inf hJR hJ₂) inf_le_left
  have hG₁J : G₁ ≤ normalizer (elementaryAbelianMaxJ R : Set G) :=
    (twoCore_normalized G₁).trans (Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ R)
  have hG₂J : G₂ ≤ normalizer (elementaryAbelianMaxJ R : Set G) := by
    rw [← hJQ]
    exact (intersection_normalized_of_centralizes d hc).trans (Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ Q)
  exact elementaryAbelianMaxJ_ne_bot_of_finite_pGroup R (isPGroup_pCoreIn 2 G₁) hRne
    (d.eq_bot_of_normalized hJR hG₁J hG₂J)

theorem source_residual_eq_commutator_thompson_core
    (d : QRCConfiguration G₁ G₂ T V) (hne : V ≠ ⊥)
    (hc : intersectionClosure G₁ G₂ ≤ centralizer (V : Set G)) :
    (pResidual 2 G₂).map G₂.subtype =
      ⁅(pResidual 2 G₂).map G₂.subtype,elementaryAbelianMaxJ (twoCoreIn G₁)⁆ := by
  let := d.finite_right
  let J := elementaryAbelianMaxJ (twoCoreIn G₁)
  let J0 := J.subgroupOf G₂
  have hJR : J ≤ twoCoreIn G₁ := sSup_le fun _ hA => hA.1
  have hJT : J ≤ T := hJR.trans (left_core_le_sylow d)
  have hJH : J ≤ G₂ := hJT.trans (sylow_le_right d)
  obtain ⟨S,hS⟩ := d.sylow_right
  have hP := intrinsic_minimalParabolic_of_coreClosure_centralizes d hne hc S hS
  have hJS : J0 ≤ S := by
    intro j hj
    have hjt : (j : G) ∈ T := hJT hj
    rw [← hS] at hjt
    obtain ⟨s,hs,he⟩ := hjt
    exact G₂.subtype_injective he ▸ hs
  have hTJ : T ≤ normalizer (J : Set G) :=
    ((sylow_le_left d).trans (twoCore_normalized G₁)).trans (Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ _)
  have hSJ : (S : Subgroup G₂) ≤ normalizer (J0 : Set G₂) := by
    apply le_normalizer_iff.mpr
    intro s hs j hj
    exact le_normalizer_iff.mp hTJ s (hS ▸ mem_map_of_mem G₂.subtype hs) j hj
  have hJnot : ¬ J0 ≤ pCore 2 G₂ := by
    intro h
    apply source_thompson_core_not_le_right_core d hne hc
    have hm := map_mono (f := G₂.subtype) h
    rwa [map_subgroupOf_eq_of_le hJH] at hm
  have he := ChapterB.minimalParabolic_residual_commutator_of_normalized_two_actor S hP J0 hJS hSJ hJnot
  have hm := congrArg (map G₂.subtype) he
  simpa only [J0,J,map_commutator,map_subgroupOf_eq_of_le hJH] using hm

private theorem image_isFF_of_maxJ_not_centralizes
    (H R W : Subgroup G) [Finite H] (hRH : R ≤ H) (hWR : W ≤ R)
    (hn : H ≤ normalizer (W : Set G)) [IsElementaryAbelian 2 W]
    (hJ : ¬ elementaryAbelianMaxJ R ≤ centralizer (W : Set G)) :
    Representation.BinaryOffender.IsFFModule (imageRepresentation H W hn) := by
  let W0 := W.subgroupOf H
  let : W0.Normal := normal_subgroupOf_of_le_normalizer hn
  let : IsElementaryAbelian 2 W0 := IsElementaryAbelian.subgroupOf (hWR.trans hRH)
  let f := actionHom H W hn
  let q := f.rangeRestrict
  have hq : Function.Surjective q := f.rangeRestrict_surjective
  let : Finite W := Finite.of_injective (inclusion (hWR.trans hRH))
    (inclusion_injective (hWR.trans hRH))
  let : Finite f.range := Finite.of_surjective q hq
  have hk : q.ker = centralizer (W0 : Set H) := by
    rw [MonoidHom.ker_rangeRestrict,actionHom_ker]
    ext g
    constructor
    · intro hg w hw
      exact Subtype.ext (hg w hw)
    · intro hg w hw
      exact congrArg H.subtype (hg ⟨w,(hWR.trans hRH) hw⟩ hw)
  have hJR : ¬ elementaryAbelianMaxJ (R.subgroupOf H) ≤ q.ker := by
    intro hh
    apply hJ
    have hm := map_mono (f := H.subtype) hh
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hRH] at hm
    intro x hx
    obtain ⟨g,hg,rfl⟩ := hm hx
    change g ∈ f.rangeRestrict.ker at hg
    rw [MonoidHom.ker_rangeRestrict,actionHom_ker] at hg
    exact hg
  let ρ := Representation.NormalElementaryQuotient.representation W0 q hq hk
  have hff : Representation.BinaryOffender.IsFFModule ρ :=
    Representation.NormalElementaryQuotient.isFFModule_of_thompson_not_le W0 q hq hk
      (R.subgroupOf H) (fun w hw => hWR hw) hJR
  let e := subgroupOfEquivOfLe (hWR.trans hRH)
  let E : Additive W0 ≃ₗ[ZMod 2] Additive W :=
    LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
  apply hff.map_equivariant ρ (imageRepresentation H W hn)
    (MonoidHom.id _) Function.injective_id E
  intro a w
  obtain ⟨g,rfl⟩ := hq a
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((ρ (q g) w).toMul.val : G) = (g : G) * (w.toMul.val : G) * (g : G)⁻¹
  exact congrArg H.subtype
    (Representation.NormalElementaryQuotient.representation_apply W0 q hq hk g w)


theorem source_residual_module_isFF
    (d : QRCConfiguration G₁ G₂ T V) (hV : V ≤ twoCoreIn G₂)
    (hu : HasUniqueNoncentralChiefFactor G₂ V)
    (hc : intersectionClosure G₁ G₂ ≤ centralizer (V : Set G)) :
    letI := residual_module_elementary d hV hc
    Representation.BinaryOffender.IsFFModule
      (imageRepresentation G₂ (⁅conjugateSpan G₂ V,(pResidual 2 G₂).map G₂.subtype⁆)
        (residual_module_normalized d)) := by
  let := d.finite_right
  let := residual_module_elementary d hV hc
  let U := conjugateSpan G₂ V
  let K := (pResidual 2 G₂).map G₂.subtype
  let I := ⁅U,K⁆
  let R := twoCoreIn G₁
  let J := elementaryAbelianMaxJ R
  let f := actionHom G₂ I (residual_module_normalized d)
  have hRH : R ≤ G₂ := (left_core_le_sylow d).trans (sylow_le_right d)
  have hIR : I ≤ R := (residual_module_le_span d).trans
    ((span_le_intersectionClosure d hV).trans
      ((intersectionClosure_eq_of_centralizes d hc).le.trans inf_le_left))
  have hKHnot : ¬ pResidual 2 G₂ ≤ f.ker := by
    intro hk
    have hic : I ≤ centralizer (K : Set G) := by
      intro i hi r hr
      obtain ⟨r,hr,rfl⟩ := hr
      have hh := hk hr
      rw [actionHom_ker] at hh
      exact (hh i hi).symm
    have he := commutator_eq_bot_iff_le_centralizer.mpr hic
    have hid : ⁅I,K⁆ = I := residual_commutator_idempotent d hV
    exact residual_commutator_ne_bot d (module_ne_bot hu) (hid.symm.trans he)
  obtain ⟨S,hS⟩ := d.sylow_right
  have hP := intrinsic_minimalParabolic_of_coreClosure_centralizes d (module_ne_bot hu) hc S hS
  have hker : f.ker ≤ ChapterB.minimalParabolicCore S hP :=
    ChapterB.minimalParabolic_normal_le_core_of_residual_not_le S hP f.ker hKHnot
  have hJR : J ≤ R := sSup_le fun _ hA => hA.1
  have hJnot : ¬ J ≤ centralizer (I : Set G) := by
    intro hj
    apply source_thompson_core_not_le_right_core d (module_ne_bot hu) hc
    intro j hjJ
    let jH : G₂ := ⟨j,hRH (hJR hjJ)⟩
    have hjS : jH ∈ S := by
      have ht := (left_core_le_sylow d) (hJR hjJ)
      rw [← hS] at ht
      obtain ⟨s,hs,he⟩ := ht
      change G₂.subtype s = G₂.subtype jH at he
      exact G₂.subtype_injective he ▸ hs
    have hjC : jH ∈ f.ker := by
      rw [actionHom_ker]
      exact hj hjJ
    have hjcore : jH ∈ pCore 2 G₂ := by
      rw [← ChapterB.minimalParabolic_sylow_inf_core S hP]
      exact ⟨hjS,hker hjC⟩
    exact mem_map_of_mem G₂.subtype hjcore
  exact image_isFF_of_maxJ_not_centralizes G₂ R I hRH hIR (residual_module_normalized d) hJnot

theorem source_residual_module_image_core_eq_bot
    (d : QRCConfiguration G₁ G₂ T V) (hV : V ≤ twoCoreIn G₂)
    (hu : HasUniqueNoncentralChiefFactor G₂ V)
    (hc : intersectionClosure G₁ G₂ ≤ centralizer (V : Set G)) :
    pCore 2 (internalActionImage G₂ (⁅conjugateSpan G₂ V,(pResidual 2 G₂).map G₂.subtype⁆)
      (residual_module_normalized d)) = ⊥ := by
  let I := ⁅conjugateSpan G₂ V,(pResidual 2 G₂).map G₂.subtype⁆
  let I0 := I.subgroupOf G₂
  let f := actionHom G₂ I (residual_module_normalized d)
  have hIH : I ≤ G₂ := (residual_module_le_span d).trans
    ((span_le_right_core d hV).trans (twoCore_le G₂))
  let : I0.Normal := normal_subgroupOf_of_le_normalizer (residual_module_normalized d)
  have hk : f.ker = centralizer (I0 : Set G₂) := by
    rw [actionHom_ker]
    ext g
    constructor
    · intro hg i hi
      exact Subtype.ext (hg i hi)
    · intro hg i hi
      exact congrArg G₂.subtype (hg ⟨i,hIH hi⟩ hi)
  have hzero : pCore 2 (G₂ ⧸ f.ker) = ⊥ := by
    have hzC : pCore 2 (G₂ ⧸ centralizer (I0 : Set G₂)) = ⊥ :=
      (source_residual_module_reduced d hV hu hc).quotient_pCore_eq_bot
    have he := pCore_map_iso 2 (QuotientGroup.quotientMulEquivOfEq hk.symm)
    rw [hzC,Subgroup.map_bot] at he
    exact he.symm
  have hm := pCore_map_iso 2 (QuotientGroup.quotientKerEquivRange f)
  rw [hzero,Subgroup.map_bot] at hm
  exact hm.symm

theorem source_containsReducedFF
    (d : QRCConfiguration G₁ G₂ T V) (hV : V ≤ twoCoreIn G₂)
    (hu : HasUniqueNoncentralChiefFactor G₂ V)
    (hc : intersectionClosure G₁ G₂ ≤ centralizer (V : Set G)) :
    ContainsReducedFF G₂ (conjugateSpan G₂ V) := by
  refine ⟨⁅conjugateSpan G₂ V,(pResidual 2 G₂).map G₂.subtype⁆,
    residual_module_le_span d,
    (residual_module_le_span d).trans ((span_le_right_core d hV).trans (twoCore_le G₂)),
    residual_module_normalized d,residual_module_elementary d hV hc,?_,?_⟩
  · exact source_residual_module_image_core_eq_bot d hV hu hc
  · exact source_residual_module_isFF d hV hu hc


theorem source_thompson_eq_of_notFF
    (d : QRCConfiguration G₁ G₂ T V)
    (hnf : letI := d.module_elementary
      ¬ Representation.BinaryOffender.IsFFModule (imageRepresentation G₁ V d.module_normalized)) :
    elementaryAbelianMaxJ T = elementaryAbelianMaxJ (twoCoreIn G₁) := by
  let := d.finite_left
  let := d.module_elementary
  let : Finite T := Finite.of_injective (inclusion (sylow_le_left d))
    (inclusion_injective (sylow_le_left d))
  have hJT : elementaryAbelianMaxJ T ≤ T := sSup_le fun _ hA => hA.1
  have hJV : elementaryAbelianMaxJ T ≤ centralizer (V : Set G) := by
    by_contra hc
    exact hnf (image_isFF_of_maxJ_not_centralizes G₁ T V (sylow_le_left d)
      (d.module_le_core.trans (left_core_le_sylow d)) d.module_normalized hc)
  have hJR : elementaryAbelianMaxJ T ≤ twoCoreIn G₁ := by
    rw [d.core_eq_centralizer]
    exact le_inf hJT hJV
  exact (elementaryAbelianMaxJ_eq_of_intermediate_finite T (twoCoreIn G₁) hJR
    (left_core_le_sylow d)).symm

theorem source_structuralConclusion_of_notFF
    (d : QRCConfiguration G₁ G₂ T V) (hV : V ≤ twoCoreIn G₂)
    (hu : HasUniqueNoncentralChiefFactor G₂ V)
    (hc : intersectionClosure G₁ G₂ ≤ centralizer (V : Set G))
    (hnf : letI := d.module_elementary
      ¬ Representation.BinaryOffender.IsFFModule (imageRepresentation G₁ V d.module_normalized)) :
    StructuralConclusion G₁ G₂ T V :=
  ⟨intersection_normalized_of_centralizes d hc,
    span_elementary_of_centralizes d hV hc,
    source_residual_module_centralizes_core d hV hu hc,
    source_residual_eq_commutator_thompson_core d (module_ne_bot hu) hc,
    source_thompson_eq_of_notFF d hnf,source_containsReducedFF d hV hu hc⟩

theorem source_uniqueFactor_cases
    (d : QRCConfiguration G₁ G₂ T V) (hV : V ≤ twoCoreIn G₂)
    (hu : HasUniqueNoncentralChiefFactor G₂ V) :
    letI := d.module_elementary
    let ρ := imageRepresentation G₁ V d.module_normalized
    (Representation.BinaryOffender.quadraticRatio ρ ≤ 1 ∧
      Representation.BinaryOffender.IsFFModule ρ) ∨
      DualFF d ∨ StructuralConclusion G₁ G₂ T V := by
  let := d.module_elementary
  let := d.finite_left
  let : Finite V := Finite.of_injective (inclusion d.module_le) (inclusion_injective d.module_le)
  let f := actionHom G₁ V d.module_normalized
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let ρ := imageRepresentation G₁ V d.module_normalized
  by_cases hff : Representation.BinaryOffender.IsFFModule ρ
  · exact Or.inl ⟨(Representation.BinaryOffender.isFFModule_iff_quadraticRatio_le_one ρ).mp hff,hff⟩
  · right
    rcases source_dualFF_or_coreClosure_centralizes d hV hu with hf | hc
    · exact Or.inl hf
    · exact Or.inr (source_structuralConclusion_of_notFF d hV hu hc hff)

end CFSG.Quasithin.ChapterD.UniqueFactor
