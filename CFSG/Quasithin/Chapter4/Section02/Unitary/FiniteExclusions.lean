module
public import CFSG.Quasithin.ChapterC.Section04.A5FiniteNormality
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedRankOne
public import Theory.GroupTheory.ConjugateSpanSimpleImage
public import Theory.GroupTheory.PerfectLargeTwoNormalizer
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity

/-!
# Finite component exclusions for the original unitary residual

The perfect residual with quotient G₂(2)′ retains its simple section in
any nontrivial image. Therefore 6048 divides the order of its action on an
escaping component, and also the order of the component's central quotient.
This excludes A₅–A₈, the triple cover of A₆, and binary SL₅. In the remaining
equal-order G₂(2)′ row, the action is the whole inner group. It cannot
normalize the nontrivial two-group induced by the original radical.

All actions and star maps are those of the genuine C.2.8 configuration.
No normality of the seed or component is needed for these exclusions.
Source: Aschbacher–Smith C.2.7 and C.4.5–8, pp.145–147,152–154,
in the original 4.2.12–13 pushing-up configuration, pp.610–612.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}
local notation "D" => commutator (Atlas.G2.Model (ZMod 2))

/-- The actual simple unitary section persists in every nontrivial span image. -/
theorem unitary_span_hom_eq_one_of_order_not_dvd
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (e : L ⧸ pCore 2 L ≃* D) {Q : Type*} [Group Q]
    (hQ : ¬ 6048 ∣ Nat.card Q) (f : conjugateSpanBy L M →* Q) : f = 1 := by
  let : IsSimpleGroup D := Atlas.G2.isSimple_commutator_binary
  let := h.component.perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe h.component_le).toMonoidHom)
    (subgroupOfEquivOfLe h.component_le).surjective
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : q.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent (pCore 2 L) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable q.ker := hq ▸ inferInstance
  apply conjugateSpanBy_hom_eq_one L M ?_ f
  intro g
  apply hom_eq_one_of_simple_quotient_card_dvd q
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) (p := 6048) ?_ hQ g
  rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]

/-- The order divisor is retained in the literal nontrivial component action. -/
theorem unitary_component_action_order_dvd
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (e : L ⧸ pCore 2 L ≃* D)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) :
    6048 ∣ Nat.card (coreCentralActorImage K ((conjugateSpanBy L M).subgroupOf H)) := by
  let X := conjugateSpanBy L M
  let A := X.subgroupOf H
  let N := normalizer (K : Set H)
  let B := coreCentralActorImage K A
  have hXH : X ≤ H := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  have hAN : A ≤ N := h.constrained_span_normalizes_intrinsic K hK hq
  let ex := (subgroupOfEquivOfLe hXH).symm.trans (subgroupOfEquivOfLe hAN).symm
  let q : X →* B := ((normalizerCoreCentralAction K).subgroupMap (A.subgroupOf N)).comp
    ex.toMonoidHom
  have hs : Function.Surjective q :=
    ((normalizerCoreCentralAction K).subgroupMap_surjective _).comp ex.surjective
  by_contra hd
  have he := h.unitary_span_hom_eq_one_of_order_not_dvd e hd q
  apply h.constrained_span_action_nontrivial K hK hq hout
  apply eq_bot_iff.mpr
  intro b hb
  obtain ⟨x,hx⟩ := hs ⟨b,hb⟩
  exact congrArg Subtype.val (hx.symm.trans (DFunLike.congr_fun he x))

/-- Soluble outer automorphisms place the same order divisor inside the
component's actual central quotient. -/
theorem unitary_component_central_order_dvd
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (e : L ⧸ pCore 2 L ≃* D)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) : 6048 ∣ Nat.card (coreCentralQuotient K) := by
  let := hq
  let Q := coreCentralQuotient K
  let : IsSimpleGroup Q := hq.simple
  let X := conjugateSpanBy L M
  let A := X.subgroupOf H
  let B := coreCentralActorImage K A
  have hXH : X ≤ H := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  let := h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hXH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hXH).symm.surjective
  let : Group.IsPerfect B := coreCentralActorImage_perfect K A
    (h.constrained_span_normalizes_intrinsic K hK hq)
  let : Group.IsSolvable (MulAut.Outer Q) := h.constrained_core_central_outer_solvable K hq
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp hc)).elim
  obtain ⟨f,hf,_⟩ := MulAut.perfect_subgroup_exists_inner_lift B hz
  exact (h.unitary_component_action_order_dvd e K hK hq hout).trans
    (card_dvd_of_injective f hf)

/-- Equal order would make the seed action the whole inner group, which
cannot normalize the nontrivial action of the original radical. -/
theorem no_unitary_constrained_central_small
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (e : L ⧸ pCore 2 L ≃* D)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (hcard : Nat.card (coreCentralQuotient K) ≤ 6048) : False := by
  let := hq
  let Q := coreCentralQuotient K
  let : IsSimpleGroup Q := hq.simple
  let X := conjugateSpanBy L M
  let A := X.subgroupOf H
  let B := coreCentralActorImage K A
  let U := coreCentralActorImage K (R.subgroupOf H)
  have hXH : X ≤ H := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  let := h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hXH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hXH).symm.surjective
  let : Group.IsPerfect B := coreCentralActorImage_perfect K A
    (h.constrained_span_normalizes_intrinsic K hK hq)
  let : Group.IsSolvable (MulAut.Outer Q) := h.constrained_core_central_outer_solvable K hq
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp hc)).elim
  have hb : Nat.card Q ≤ Nat.card B := hcard.trans
    (Nat.le_of_dvd (Nat.card_pos) (h.unitary_component_action_order_dvd e K hK hq hout))
  have hAR : A ≤ normalizer (R.subgroupOf H : Set H) := by
    intro a ha r
    exact h.span_normalizes_radical ha (r : G)
  have hU : IsPGroup 2 U := h.isRadical.isPGroup.comap_subtype.map _
  exact h.constrained_radical_action_nontrivial K hK hq hout hfK
    (MulAut.perfect_normalizer_two_eq_bot_of_card_le hz B U hb hU
      (coreCentralActorImage_normalizes K A (R.subgroupOf H) hAR))

private theorem alternating_small_order_not_dvd {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≤ 8) :
    ¬ 6048 ∣ Nat.card (alternatingGroup (Fin n)) := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [nat_card_alternatingGroup, Nat.card_fin]
  interval_cases n <;> norm_num [Nat.factorial]

/-- All alternating star rows in C.2.7 are too small in their cubic part. -/
theorem no_unitary_constrained_alternating
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≤ 8)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃*
      alternatingGroup (Fin n)) : False := by
  let ec := (coreCentralQuotientCongr
    (K.equivMapOfInjective H.subtype H.subtype_injective)).trans
      (Section04Constrained.source_simple_equiv
        (h.constrained_source_input K hK hq hout hfK) e
        (alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ n by omega))))
  have hd := h.unitary_component_central_order_dvd a K hK hq hout
  rw [Nat.card_congr ec.toEquiv] at hd
  exact alternating_small_order_not_dvd hn hn8 hd

/-- The triple-six row has the same excluded central quotient A₆. -/
theorem no_unitary_constrained_triple_six
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (e : (starImage (K.map H.subtype) R (K.map H.subtype) ⧸
      center (starImage (K.map H.subtype) R (K.map H.subtype))) ≃*
      alternatingGroup (Fin 6)) : False := by
  let ec := (h.constrained_star_central_equiv K hK hq hout hfK).trans e
  have hd := h.unitary_component_central_order_dvd a K hK hq hout
  rw [Nat.card_congr ec.toEquiv,nat_card_alternatingGroup] at hd
  norm_num [Nat.factorial] at hd

private theorem linear_five_small_order_not_dvd
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 2) :
    ¬ 6048 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 5) F) := by
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
  norm_num [hF,Fin.prod_univ_succ] at hc
  rw [hc]
  decide

/-- Binary SL₅ has only 3² in its order, whereas the unitary seed retains 3³. -/
theorem no_unitary_constrained_linear_five_two
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃*
      Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) : False := by
  let ec := (h.constrained_star_central_equiv K hK hq hout hfK).trans
    (QuotientGroup.congr _ _ e (FixedElementary.map_center e))
  have hd := h.unitary_component_central_order_dvd a K hK hq hout
  rw [Nat.card_congr ec.toEquiv] at hd
  exact linear_five_small_order_not_dvd (by simp : Nat.card (ZMod 2) = 2) hd

/-- The remaining binary G₂-derived row is excluded by the full inner action. -/
theorem no_unitary_constrained_g2_derived_two
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* D) : False := by
  let ec := (coreCentralQuotientCongr
    (K.equivMapOfInjective H.subtype H.subtype_injective)).trans
      (Section04Constrained.source_simple_equiv
        (h.constrained_source_input K hK hq hout hfK) e
        Theory.SpecificGroups.g2_derived_two_center_eq_bot)
  apply h.no_unitary_constrained_central_small a K hK hq hout hfK
  rw [Nat.card_congr ec.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]

end CFSG.Quasithin.ChapterC.HypothesisC28
