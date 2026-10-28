module

public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourcePlacement
public import Theory.GroupTheory.PerfectMovedElementaryRank
public import CFSG.Quasithin.ChapterA.Section02.OddModelTwoRank

/-!
# Excluding the ordinary odd-characteristic rows in C.3.1

The original module V lies in the ordinary component and is not central there.
Its image in the component's central quotient is consequently nontrivial,
elementary abelian, and equal to its commutator with the perfect image of the
original conjugate span. Thus this quotient has two-rank at least three.
The three odd-characteristic rows of Theorem C all have two-rank at most two.

This is the odd-characteristic exclusion in Aschbacher--Smith C.3.1, printed
p.151. It uses the actual quotient map and module, and requires no A₅ marking
or normalization of the original source component by M.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G]
variable {H M L R V : Subgroup G}

/-- The image of the original moved module forces two-rank at least three
in every ordinary component's literal central quotient. -/
theorem ordinary_quotient_twoRank_ge_three
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K) :
    3 ≤ primeRank 2 (K ⧸ center K) := by
  let X := conjugateSpanBy L M
  let A := X.subgroupOf H
  let U := V.subgroupOf H
  let AK := A.subgroupOf K
  let UK := U.subgroupOf K
  let q := QuotientGroup.mk' (center K)
  have hXH : X ≤ H := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  have hVH : V ≤ H := h.module_le.trans hXH
  have hAK : A ≤ K := h.ordinary_span_le K hK
  have hUA : U ≤ A := subgroupOf_mono H h.module_le
  have hUK : U ≤ K := hUA.trans hAK
  let e : AK ≃* X := (subgroupOfEquivOfLe hAK).trans (subgroupOfEquivOfLe hXH)
  let := h.span_perfect
  let : Group.IsPerfect AK := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsPerfect (AK.map q) := Group.IsPerfect.map q
  let := h.module_elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVH
  let : IsElementaryAbelian 2 UK := IsElementaryAbelian.subgroupOf hUK
  let : IsElementaryAbelian 2 (UK.map q) := IsElementaryAbelian.map q
  have hmoveH : U = ⁅U,A⁆ := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVH,map_subgroupOf_eq_of_le hXH]
    exact h.module_commutator
  have hmoveK : UK = ⁅UK,AK⁆ := by
    apply map_injective K.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hUK,map_subgroupOf_eq_of_le hAK]
    exact hmoveH
  have hmove : UK.map q = ⁅UK.map q,AK.map q⁆ := by
    rw [← map_commutator,← hmoveK]
  have hne : UK.map q ≠ ⊥ := by
    intro he
    have hc : UK ≤ center K := by
      simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff UK).mp he
    apply h.ordinary_module_not_centralizes K hK
    intro u hu k hk
    exact congrArg (fun x : K => (x : H))
      (mem_center_iff.mp (hc (show (⟨u,hUK hu⟩ : K) ∈ UK from hu)) ⟨k,hk⟩)
  exact three_le_primeRank_of_perfect_moved_elementary (AK.map q) (UK.map q)
    (map_mono (subgroupOf_mono K hUA)) hne hmove

/-- The full ordinary odd-characteristic catalogue is impossible under
the genuine C.2.8 hypotheses, without any A₅ specialization. -/
theorem no_ordinary_component_of_theoremC_odd_model
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K)
    (hm : ChapterA.Section02.IsTheoremCOddModel (K ⧸ center K)) : False := by
  have hl := h.ordinary_quotient_twoRank_ge_three K hK
  have hu := hm.twoRank_le_two
  omega

end CFSG.Quasithin.ChapterC.HypothesisC28
