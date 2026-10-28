module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalComponents
public import CFSG.Quasithin.Chapter13.Section07.FixedLayerCatalogue
public import Theory.SpecificGroups.BinaryComponentResidual
public import Theory.GroupTheory.CComponent.RankTwoResidual

/-!
# The original selected component has a small quotient

The selected component cannot contain the point residual, which is generated
by its elements of order three. A centerless rank-two component with outer
2-group would be the entire three-residual of H, contradicting that selection.
This excludes A6 and PSU3(3), the latter through its proved G2(2)' comparison.
Simplicity excludes the triple cover of A6. The earlier five-model list therefore
leaves exactly A5 and PSL3(2), and gives normality on the actual kernel subgroup.

The source classification input remains explicit: `Source1332OneTwo` is not
proved here. Its selected five-model consequence suffices; no later plus-kernel
faithfulness or small-offender catalogue is used in this reduction.

Source: Aschbacher--Smith, 13.3.2(1--2), A.3.18 and 13.7.4(1),
printed pp.884--885 and 937.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction
open Section08.SourceCompletion Section03.Noncentrality.SupercriticalSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

omit d [Finite G] in
private theorem quotient_quasisimple
    (J : Subgroup H) (hJ : J.IsCComponent) (hs : IsSimpleGroup (J ⧸ pCore 2 J)) :
    IsQuasisimple (J ⧸ pCore 2 J) := by
  let := hs
  let : Group.IsPerfect J := hJ.perfect
  let : Group.IsPerfect (J ⧸ pCore 2 J) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hz : center (J ⧸ pCore 2 J) = ⊥ := center_eq_bot_of_simple_perfect
  exact { toIsPerfect := inferInstance
          simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }

/-- The actual point residual prevents a rank-two, outer-two quotient model. -/
theorem source_component_rankTwo_excluded
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (J : Subgroup H) (hJ : J.IsCComponent) (hs : IsSimpleGroup (J ⧸ pCore 2 J))
    (hout : ¬ (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ≤ J.map H.subtype)
    (hf : Theory.SpecificGroups.BinaryComponentResidual.Facts (J ⧸ pCore 2 J)) : False := by
  let : IsQuasisimple (J ⧸ pCore 2 J) := quotient_quasisimple J hJ hs
  have he := hJ.eq_primeToResidual_three_of_rank_outer_two hf.1 hf.2.1
    (source_H_stronglyQuasithin d h 3 (by decide) (by decide)) hf.2.2
  apply hout
  rw [source_local_residual_eq d h, ← ModelExclusions.point_residual_cubic_generated d]
  apply (closure_le _).mpr
  rintro x ⟨hx,horder⟩
  have hxH : x ∈ H := (le_sup_left.trans h.local_le)
    ((source_local_residual_eq d h).symm ▸ hx)
  have hxp : (⟨x,hxH⟩ : H) ∈ primeToResidual 3 H := by
    apply mem_primeToResidual_of_pow (n := 1)
    have ho : orderOf (⟨x,hxH⟩ : H) = 3 := (H.orderOf_coe _).symm.trans horder
    simpa only [pow_one,ho] using pow_orderOf_eq_one (⟨x,hxH⟩ : H)
  exact ⟨⟨x,hxH⟩,he.symm ▸ hxp,rfl⟩

/-- Only the five-model assertion for this selected subgroup is needed. -/
theorem source_component_small_models_of_midSize
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (J : Subgroup H) (hJ : J.IsCComponent) (hs : IsSimpleGroup (J ⧸ pCore 2 J))
    (hout : ¬ (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ≤ J.map H.subtype)
    (hm : MidSizeModel (Chapter1.XiQuotient (J.map H.subtype))) :
    Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) ∨
      ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 2 := by
  let eJ := J.equivMapOfInjective H.subtype H.subtype_injective
  let e : (J ⧸ pCore 2 J) ≃* Chapter1.XiQuotient (J.map H.subtype) :=
    QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ)
  rcases hm with ⟨⟨f⟩⟩ | ⟨F,_,_,hF,⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨_,⟨z⟩,_⟩ |
    ⟨F,_,_,A,hF,hA,⟨f⟩⟩
  · exact Or.inl ⟨e.trans f⟩
  · exact Or.inr ⟨F,inferInstance,inferInstance,hF,⟨e.trans f⟩⟩
  · exact (source_component_rankTwo_excluded d h J hJ hs hout
      (Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv (e.trans f)
        Theory.SpecificGroups.BinaryComponentResidual.alternatingSix)).elim
  · let := hs
    let : IsQuasisimple (J ⧸ pCore 2 J) := quotient_quasisimple J hJ hs
    have hz : center (J ⧸ pCore 2 J) = ⊥ := center_eq_bot_of_simple_perfect
    have hc := Nat.card_congr ((centerCongr e).trans z).toEquiv
    rw [hz,card_bot] at hc
    norm_num at hc
  · exact (source_component_rankTwo_excluded d h J hJ hs hout
      (Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv
        ((e.trans f).trans (A.projectiveEquivBinaryG2Derived hF hA))
        Theory.SpecificGroups.BinaryComponentResidual.g2)).elim

/-- The actual fixed-layer movement puts the selected subgroup in the faithful
family. The named earlier source list then reduces to A5 or PSL3(2). -/
theorem source_component_small_models
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (h1332 : Source1332OneTwo T)
    (J : Subgroup H) (hJ : J.IsCComponent) (hs : IsSimpleGroup (J ⧸ pCore 2 J))
    (hout : ¬ (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ≤ J.map H.subtype)
    (hmove : ⁅fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H),J.map H.subtype⁆ ≠ ⊥) :
    Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) ∨
      ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 2 := by
  let : IsElementaryAbelian 2 V := NaturalAction.elementary d
  let : IsElementaryAbelian 2 V₃ := IsElementaryAbelian.of_le d.seed_le
  let : IsMulCommutative (conjugateSpanBy V₃ H) := hU
  have hf := component_faithful_of_fixedLayer_movement h
    (conjugateSpanBy_elementary_of_commutative V₃ H) J hJ hmove
  exact source_component_small_models_of_midSize d h J hJ hs hout (h1332 _ hf).2

/-- Literal selected-kernel consumer: the reduced model list supplies cubic
normality on the original subgroup J of H, with its original ambient image. -/
theorem source_primitive_kernel_small_models_and_normal
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (h1332 : Source1332OneTwo T)
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (J : Subgroup H) (hJ : J.IsCComponent) (hs : IsSimpleGroup (J ⧸ pCore 2 J))
    (hKC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hmove : ⁅fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H),J.map H.subtype⁆ ≠ ⊥) :
    (Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) ∨
      ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 2) ∧
      J.Normal ∧ H ≤ normalizer (J.map H.subtype : Set G) := by
  have hout : ¬ (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ≤ J.map H.subtype :=
    fun hh => local_residual_not_le_kernel d h hne (hh.trans hKC)
  have hm := source_component_small_models d h hU h1332 J hJ hs hout hmove
  exact ⟨hm,source_primitive_kernel_normal_of_small_model d h hne J hJ hs hKC hm⟩

end CFSG.Quasithin.Chapter13.Section07.PlusAction
