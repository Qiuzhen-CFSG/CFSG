module
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalization

/-!
# The actual fixed-space commutator in C.4.8

For a constrained escaping component K under the genuine C.2.8 hypotheses,
the entire original module V lies in U = Ω₁(Z(O₂(KR))). Indeed, the radical
contains O₂(KR), and V centralizes that radical. The self-centralizing
two-core of KR therefore puts V inside the core; its exponent and centrality
put it in U. The original span M₀ also has its two-core inside the radical,
so V = [V,M₀] lies in [C_U(O₂(M₀)),M₀]. This is an invariant subgroup of U.

Every group remains in the original ambient group; U is the literal star
module, with its full centralizer kernel. The argument supplies the input
to the final parabolic module restriction in C.4.8. It does not identify
M₀ with a marked parabolic residual or assert the remaining module rows.

Source: Aschbacher--Smith C.4.8, printed p.154, using C.2.7 and C.2.9.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {H M L R V : Subgroup G}

/-- The whole original span has its two-core inside the same radical. -/
theorem span_core_le_radical
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V) :
    (conjugateSpanBy L M).pCoreIn 2 ≤ R := by
  rw [←h.span_join_core]
  exact pCoreIn_mono_of_normalizes le_sup_left
    (sup_le (conjugateSpanBy L M).le_normalizer
      (h.radical_le.trans (le_normalizer_conjugateSpanBy L M)))

/-- The whole original module lies in the literal omega-center of O₂(KR). -/
theorem constrained_module_le_starV
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    V ≤ (starV (K.map H.subtype) R).map (K.map H.subtype ⊔ R).subtype := by
  let Kg := K.map H.subtype
  let J := Kg ⊔ R
  have hi := h.constrained_source_input K hK hq hout hfK
  have hr := C27Source.source_relative_radical hi
  have hQR : pCore 2 J ≤ R.subgroupOf J :=
    pCore_le_of_pCore_normalizer_le _ hr.isPGroup hr.2.le
  have hc : centralizer (pCore 2 Kg : Set Kg) ≤ pCore 2 Kg := by
    rw [←hi.fitting]
    exact centralizer_generalizedFitting_le Kg
  have hJc := centralizer_pCore_sup_le 2 Kg R hc h.radical_isTwoGroup hi.normalizes
  let : IsElementaryAbelian 2 V := h.module_elementary
  intro v hv
  obtain ⟨z,hz,hzv⟩ := h.module_le_center_radical hv
  have hvc (r : R) : (r : G) * v = v * r := by
    rw [←hzv]
    exact congrArg Subtype.val (mem_center_iff.mp hz r)
  let vJ : J := ⟨v,mem_sup_right (hzv ▸ z.property)⟩
  have hvC : vJ ∈ centralizer (pCore 2 J : Set J) := by
    intro r hr
    exact Subtype.ext (hvc ⟨r,hQR hr⟩)
  refine ⟨vJ,?_,rfl⟩
  change vJ ∈ omegaOneCenterAmbient (pCore 2 J)
  refine (mem_omegaOneCenterAmbient_iff _ _).mpr ⟨hJc hvC,?_,hvC⟩
  have hv2 : v ^ 2 = 1 := congrArg (fun w : V => (w : G))
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) ⟨v,hv⟩)
  exact Subtype.ext hv2

/-- The actual span preserves the entire star module, with no parabolic marking. -/
theorem constrained_starV_normalized_by_span
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) :
    conjugateSpanBy L M ≤ normalizer
      ((starV (K.map H.subtype) R).map (K.map H.subtype ⊔ R).subtype : Set G) := by
  exact ((le_inf (h.component_normalized_by_span K hK) h.span_normalizes_radical).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)).trans
      (normalizer_le_normalizer_characteristic_image _ (starV _ _))

/-- The fixed-space commutator from p.154 contains the original module and
is itself an invariant subgroup of the literal star module. -/
theorem constrained_module_fixed_moved
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    let X := conjugateSpanBy L M
    let U := (starV (K.map H.subtype) R).map (K.map H.subtype ⊔ R).subtype
    let W := ⁅U ⊓ centralizer (X.pCoreIn 2 : Set G),X⁆
    V ≤ W ∧ W ≤ U ∧ X ≤ normalizer (W : Set G) := by
  let X := conjugateSpanBy L M
  let U := (starV (K.map H.subtype) R).map (K.map H.subtype ⊔ R).subtype
  have hVC : V ≤ centralizer (X.pCoreIn 2 : Set G) := by
    intro v hv x hx
    obtain ⟨z,hz,rfl⟩ := h.module_le_center_radical hv
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨x,h.span_core_le_radical hx⟩)
  have hVU := h.constrained_module_le_starV K hK hq hout hfK
  have hnU := h.constrained_starV_normalized_by_span K hK
  refine ⟨?_,?_,normalizer_commutator_ge_right _ _⟩
  · conv_lhs => rw [h.module_commutator]
    exact commutator_mono (le_inf hVU hVC) le_rfl
  · exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hnU)

end CFSG.Quasithin.ChapterC.HypothesisC28

