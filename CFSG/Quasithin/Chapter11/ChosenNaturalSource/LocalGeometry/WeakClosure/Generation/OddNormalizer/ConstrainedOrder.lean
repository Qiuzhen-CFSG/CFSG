module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.NaturalAction
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedLinearTwo
public import CFSG.Quasithin.ChapterC.Section04.A5FiniteNormality

/-!
# The constrained action is a proper inner subgroup

The perfect span acts inside the inner automorphism group of the selected
simple quotient. If this image were full, its normalization of the actual
radical action would place that nontrivial two-group inside the trivial
two-core of an automorphism overgroup. Thus its order is strictly smaller
than the component central quotient. ConstrainedModels combines this with
the original nonbinary lower bound, excluding even the equality case A₈.

Source: Aschbacher--Smith C.4.4--5, printed p.152, in the 4.4.6
pushing-up argument, printed p.620.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
variable {G : Type*} [Group G] [Finite G] {H M B R W : Subgroup G}

/-- The literal constrained action cannot be the full inner group. -/
theorem constrained_action_card_lt
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K) :
    Nat.card (coreCentralActorImage K ((conjugateSpanBy B M).subgroupOf H)) <
      Nat.card (coreCentralQuotient K) := by
  let := hq
  let Q := coreCentralQuotient K
  let : IsSimpleGroup Q := hq.simple
  let X := conjugateSpanBy B M
  let A := X.subgroupOf H
  let C := coreCentralActorImage K A
  let U := coreCentralActorImage K (R.subgroupOf H)
  have hXH : X ≤ H := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  let := h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hXH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hXH).symm.surjective
  let : Group.IsPerfect C := coreCentralActorImage_perfect K A
    (h.constrained_span_normalizes_intrinsic K hK hq)
  let : Group.IsSolvable (MulAut.Outer Q) := h.constrained_core_central_outer_solvable K hq
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp hc)).elim
  obtain ⟨f,hf,hconj⟩ := MulAut.perfect_subgroup_exists_inner_lift C hz
  have hAR : A ≤ normalizer (R.subgroupOf H : Set H) := by
    intro a ha r
    exact h.span_normalizes_radical ha (r : G)
  have hU : IsPGroup 2 U := h.isRadical.isPGroup.comap_subtype.map _
  have hCU : C ≤ normalizer (U : Set (MulAut Q)) :=
    coreCentralActorImage_normalizes K A (R.subgroupOf H) hAR
  have hproper : f.range ≠ ⊤ := by
    intro ht
    have hi : ∀ x : Q, MulAut.conj x ∈ C := by
      intro x
      obtain ⟨a,ha⟩ := (show x ∈ f.range from ht ▸ mem_top x)
      rw [←ha,hconj]
      exact a.property
    have hcore : pCore 2 Q = ⊥ := by
      rcases (inferInstance : (pCore 2 Q).Normal).eq_bot_or_eq_top with hb | ht
      · exact hb
      · have hp : IsPGroup 2 Q := IsPGroup.of_equiv
          (pCore_isPGroup (p := 2) (G := Q)) ((MulEquiv.subgroupCongr ht).trans topEquiv)
        let := hp.isNilpotent
        exact (Group.IsPerfect.not_isSolvable Q inferInstance).elim
    let J := C ⊔ U
    have hj : pCore 2 J = ⊥ := automorphism_core_eq_bot 2
      (MulAut.conj_injective_of_center_eq_bot hz) hcore J (fun x => mem_sup_left (hi x))
    have hu : U ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes hU le_sup_right
      (sup_le hCU U.le_normalizer)
    unfold Subgroup.pCoreIn at hu
    rw [hj,Subgroup.map_bot] at hu
    exact h.constrained_radical_action_nontrivial K hK hq hout hfK (bot_unique hu)
  have hc : Nat.card C = Nat.card f.range :=
    Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
  change Nat.card C < Nat.card Q
  rw [hc]
  exact lt_of_not_ge (fun hge => hproper (f.range.eq_top_of_le_card hge))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
