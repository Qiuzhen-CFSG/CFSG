module

public import CFSG.Quasithin.ChapterC.Section04.ConstrainedAction
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.Preparation
public import Theory.GroupTheory.CComponent.RadicalKernel
public import Theory.GroupTheory.PerfectAutomorphismStabilizer

/-!
# The normalized actor on a constrained component

The perfect original residual acts on the actual core-central quotient of
the constrained component. Solvability of the outer quotient realizes this
action by inner automorphisms. Its kernel is a proper normal subgroup of
the intrinsic C-component, hence soluble. The action retains the original
radical intersection and its normalizer.

Source: Aschbacher--Smith C.2.8, C.4.5 and 4.2.12--13,
printed pp.147,152,610--612.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl

/-- The actual normalized source actor is realized inside the simple
component quotient, retaining its radical normalizer and soluble kernel. -/
theorem constrained_normalized_inner_representation
    {G : Type*} [Group G] [Finite G]
    {H M F R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H) :
    ∃ r : F →* coreCentralQuotient K, Group.IsSolvable r.ker ∧
      r.range ≤ normalizer (coreCentralIntersectionImage K (R.subgroupOf H) :
        Set (coreCentralQuotient K)) := by
  let := hq
  let Q := coreCentralQuotient K
  let : IsSimpleGroup Q := hq.simple
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective
    (QuotientGroup.mk'_surjective (center (K ⧸ pCore 2 K)))
  have hspan := h.normalized_span_eq hn
  let : Group.IsPerfect F := hspan ▸ h.span_perfect
  have hFH : F ≤ H := h.component_le.trans h.local_le
  let A := F.subgroupOf H
  have hAK : A ≤ normalizer (K : Set H) := by
    simpa only [hspan] using h.constrained_span_normalizes_intrinsic K hK hq
  let B := coreCentralActorImage K A
  let e : F ≃* A.subgroupOf (normalizer (K : Set H)) :=
    (subgroupOfEquivOfLe hFH).symm.trans (subgroupOfEquivOfLe hAK).symm
  let b : F →* B := ((normalizerCoreCentralAction K).subgroupMap
    (A.subgroupOf (normalizer (K : Set H)))).comp e.toMonoidHom
  have hb : Function.Surjective b :=
    ((normalizerCoreCentralAction K).subgroupMap_surjective _).comp e.surjective
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective hb
  let : Group.IsSolvable (MulAut.Outer Q) := h.constrained_core_central_outer_solvable K hq
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp ht)).elim
  obtain ⟨f,hf,hconj⟩ := MulAut.perfect_subgroup_exists_inner_lift B hz
  let r := f.comp b
  have hne : r ≠ 1 := by
    intro he
    apply h.constrained_span_action_nontrivial K hK hq hout
    rw [hspan]
    apply bot_unique
    intro x hx
    obtain ⟨y,hy⟩ := hb ⟨x,hx⟩
    have hh : f (b y) = f 1 := (DFunLike.congr_fun he y).trans f.map_one.symm
    have hh' := hf hh
    rw [hy] at hh'
    exact congrArg B.subtype hh'
  have htop : (⊤ : Subgroup (F.subgroupOf M)).IsCComponent := by
    simpa using h.component.subgroupOf (le_refl (F.subgroupOf M))
  have htopF : (⊤ : Subgroup F).IsCComponent := by
    simpa only [map_top_of_surjective (subgroupOfEquivOfLe h.component_le).toMonoidHom (subgroupOfEquivOfLe h.component_le).surjective]
      using htop.map_equiv (subgroupOfEquivOfLe h.component_le)
  have hker := kernel_le_solvableRadical_of_top_isCComponent htopF r
    (fun ht => hne (MonoidHom.ker_eq_top_iff.mp ht))
  refine ⟨r,Group.isSolvable_of_isSolvable_injective (inclusion_injective hker),?_⟩
  have hAR : A ≤ normalizer (R.subgroupOf H : Set H) := by
    intro a ha x
    exact h.span_normalizes_radical (hspan.symm ▸ ha) (x : G)
  rintro _ ⟨x,rfl⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [show r x = f (b x) from rfl,hconj]
  exact coreCentralActorImage_stabilizes K A (R.subgroupOf H) hAR (b x).property

end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl

end
