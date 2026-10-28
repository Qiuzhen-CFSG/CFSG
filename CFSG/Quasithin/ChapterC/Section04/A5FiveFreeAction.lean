module
public import Theory.GroupTheory.ConjugateSpanSimpleImage
public import Theory.GroupTheory.PerfectAutomorphismStabilizer
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedAction
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.Tactic.NormNum

/-!
# Five-free targets of the original A₅ span action

Every homomorphism from the original conjugate span to a group of order
prime to five is trivial. Each literal seed conjugate retains the simple
A₅ section in any nontrivial image, and those conjugates generate the span.

For an escaping component, its actual core-central action is nontrivial
and perfect. The soluble outer group realizes that image faithfully inside
the simple central quotient. Hence that quotient cannot have order prime
to five. This exclusion needs no normality of the selected component and
applies directly to the SL₃(2) source row.

Source: Aschbacher–Smith C.4.3–8, printed pp.152–154, specialized to the
A₅ covering configuration of 4.2.12–13, pp.610–611.
-/

public section
open Subgroup Theory.GroupTheory

namespace Theory.GroupTheory
variable {G D : Type*} [Group G] [Finite G] [Group D]
  [Group.IsPerfect G]
private theorem a5_cover_hom_eq_one_of_five_free
    (e : G ⧸ pCore 2 G ≃* alternatingGroup (Fin 5))
    (hD : ¬ 5 ∣ Nat.card D) (f : G →* D) : f = 1 := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hq : q.ker = pCore 2 G := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent (pCore 2 G) :=
    (pCore_isPGroup (p := 2) (G := G)).isNilpotent
  let : Group.IsSolvable q.ker := hq ▸ inferInstance
  apply hom_eq_one_of_simple_quotient_card_dvd q
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) (p := 5) ?_ hD f
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]
end Theory.GroupTheory

namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}
theorem a5_span_hom_eq_one_of_fiveFree
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (e : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    {D : Type*} [Group D] (hD : ¬ 5 ∣ Nat.card D)
    (f : conjugateSpanBy L M →* D) : f = 1 := by
  let := h.component.perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe h.component_le).toMonoidHom)
    (subgroupOfEquivOfLe h.component_le).surjective
  exact conjugateSpanBy_hom_eq_one L M
    (fun g => a5_cover_hom_eq_one_of_five_free e hD g) f

theorem no_a5_component_of_central_fiveFree
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (e : L ⧸ pCore 2 L ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H)
    (hfree : ¬ 5 ∣ Nat.card (coreCentralQuotient K)) : False := by
  let := hq
  let Q := coreCentralQuotient K
  let : IsSimpleGroup Q := hq.simple
  let X := conjugateSpanBy L M
  let A := X.subgroupOf H
  let N := normalizer (K : Set H)
  let B := coreCentralActorImage K A
  have hXH : X ≤ H := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  have hAN : A ≤ N := h.constrained_span_normalizes_intrinsic K hK hq
  let := h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hXH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hXH).symm.surjective
  let : Group.IsPerfect B := coreCentralActorImage_perfect K A hAN
  let : Group.IsSolvable (MulAut.Outer Q) := h.constrained_core_central_outer_solvable K hq
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp hc)).elim
  obtain ⟨f,hf,_⟩ := MulAut.perfect_subgroup_exists_inner_lift B hz
  let ex := (subgroupOfEquivOfLe hXH).symm.trans (subgroupOfEquivOfLe hAN).symm
  let q : X →* B := ((normalizerCoreCentralAction K).subgroupMap (A.subgroupOf N)).comp
    ex.toMonoidHom
  have hq : Function.Surjective q :=
    ((normalizerCoreCentralAction K).subgroupMap_surjective _).comp ex.surjective
  have he := h.a5_span_hom_eq_one_of_fiveFree e hfree (f.comp q)
  apply h.constrained_span_action_nontrivial K hK ‹IsQuasisimple (K ⧸ pCore 2 K)› hout
  apply eq_bot_iff.mpr
  intro b hb
  obtain ⟨x,hx⟩ := hq ⟨b,hb⟩
  have hz : (⟨b,hb⟩ : B) = 1 := hf (by
    rw [←hx]
    simpa only [MonoidHom.comp_apply,MonoidHom.one_apply,map_one] using DFunLike.congr_fun he x)
  exact congrArg Subtype.val hz
end CFSG.Quasithin.ChapterC.HypothesisC28
