module
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedAction
public import Theory.GroupTheory.PerfectAutomorphismStabilizer
public import Theory.GroupTheory.PerfectSimpleImageKernel
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# The original normal seed acts inside the component central quotient

In C.2.8, a seed normal in the local intersection equals its conjugate
span. Its action on the escaping component's central core quotient is
nontrivial and perfect. Solvable outer automorphisms give an inner lift.
If the seed has a simple quotient with solvable kernel, the lift also has
solvable kernel and preserves the literal image of the radical intersection.

Source: Aschbacher--Smith, C.4.3--5, printed p.152. The Mathieu application
uses the normal intersection residual of 4.2.12--13, pp.610--612.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G S : Type*} [Group G] [Finite G] [Group S] [IsSimpleGroup S]
variable {H M L R V : Subgroup G}

/-- The normal original residual acts nontrivially inside the component's
simple quotient, with solvable kernel and the literal radical stabilizer. -/
theorem normal_seed_inner_action
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : (L.subgroupOf M).Normal)
    (q : L →* S) (hq : Function.Surjective q) [Group.IsSolvable q.ker]
    (K : Subgroup H) (hK : K.IsCComponent) (hqu : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) :
    ∃ r : L →* coreCentralQuotient K, Group.IsSolvable r.ker ∧
      r.range ≤ normalizer (coreCentralIntersectionImage K (R.subgroupOf H) : Set _) := by
  let := hqu
  let Q := coreCentralQuotient K
  let : IsSimpleGroup Q := hqu.simple
  have hspan : conjugateSpanBy L M = L := le_antisymm
    (conjugateSpanBy_le le_rfl ((normal_subgroupOf_iff_le_normalizer h.component_le).mp hn))
    (le_conjugateSpanBy _ _)
  let := h.component.perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe h.component_le).toMonoidHom)
    (subgroupOfEquivOfLe h.component_le).surjective
  let A := L.subgroupOf H
  let N := normalizer (K : Set H)
  let B := coreCentralActorImage K A
  have hLH : L ≤ H := h.component_le.trans h.local_le
  have hAN : A ≤ N := by
    simpa only [hspan] using h.constrained_span_normalizes_intrinsic K hK hqu
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hLH).symm.surjective
  let : Group.IsPerfect B := coreCentralActorImage_perfect K A hAN
  let : Group.IsSolvable (MulAut.Outer Q) := h.constrained_core_central_outer_solvable K hqu
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp hc)).elim
  obtain ⟨f,hf,hconj⟩ := MulAut.perfect_subgroup_exists_inner_lift B hz
  let ex := (subgroupOfEquivOfLe hLH).symm.trans (subgroupOfEquivOfLe hAN).symm
  let a : L →* B := ((normalizerCoreCentralAction K).subgroupMap (A.subgroupOf N)).comp ex.toMonoidHom
  have ha : Function.Surjective a :=
    ((normalizerCoreCentralAction K).subgroupMap_surjective _).comp ex.surjective
  let r := f.comp a
  have hr : r ≠ 1 := by
    intro he
    have hb : B = ⊥ := by
      apply eq_bot_iff.mpr
      intro b hb
      obtain ⟨x,hx⟩ := ha ⟨b,hb⟩
      have hh : (⟨b,hb⟩ : B) = 1 := hf (by
        rw [←hx]
        have hone : r x = 1 := DFunLike.congr_fun he x
        exact hone.trans (map_one f).symm)
      exact congrArg Subtype.val hh
    exact h.constrained_span_action_nontrivial K hK hqu hout (by simpa only [hspan] using hb)
  refine ⟨r,solvable_ker_of_nontrivial_hom_of_simple_quotient q hq r hr,?_⟩
  have hAR : A ≤ normalizer (R.subgroupOf H : Set H) := by
    intro a ha y
    exact h.span_normalizes_radical (hspan.symm ▸ ha) (y : G)
  rintro _ ⟨x,rfl⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (coreCentralIntersectionImage K (R.subgroupOf H)).map (MulAut.conj (f (a x))).toMonoidHom = _
  rw [hconj]
  exact coreCentralActorImage_stabilizes K A (R.subgroupOf H) hAR (a x).property

end CFSG.Quasithin.ChapterC.HypothesisC28
