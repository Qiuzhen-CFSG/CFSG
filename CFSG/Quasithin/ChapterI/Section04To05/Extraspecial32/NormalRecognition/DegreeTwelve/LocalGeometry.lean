module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.Interfaces
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Selected
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Census
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer

/-!
# Assembly of the local geometry and the two ambient orders

Two distinct elementary eights cannot contain one another. Thus the selected
intersection `E`, once proved different from the canonical fusion eight `F`,
contains a nonidentity involution outside the class of `z`. Thompson's order
formula then converts the two centralizer alternatives and their actual
mixed-pair counts into the two possible ambient orders.

The resulting geometry is supplied to the existing degree-twelve action
construction. The selected configuration, local census and second centralizer
alternatives are assembled below from the source hypotheses and the relative
quaternion-normality input.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 2.7–2.8, 4.1–4.3 and 4.10–4.11.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve

open Subgroup Theory.GroupTheory.TwoInvolutionClassOrder

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- An elementary intersection different from the fusion eight contains a
representative of a different ambient involution class. -/
public theorem exists_second_involution_of_intersection (d : FusionEightData z)
    (g : G) (he : IsElementaryAbelian 2 (coreIntersection z g))
    (hc : Nat.card (coreIntersection z g) = 8)
    (hne : coreIntersection z g ≠ fusionCore z) :
    ∃ t : G, t ∈ coreIntersection z g ∧ orderOf t = 2 ∧ ¬ IsConj z t := by
  classical
  have hnotle : ¬ coreIntersection z g ≤ fusionCore z := by
    intro hle
    exact hne (eq_of_le_of_card_ge hle (by rw [hc, d.card]))
  obtain ⟨t, ht, htF⟩ := Set.not_subset.mp hnotle
  have ht1 : t ≠ 1 := fun ht1 => htF (ht1 ▸ (fusionCore z).one_mem)
  let : IsElementaryAbelian 2 (coreIntersection z g) := he
  have ht2 : orderOf t = 2 :=
    (Nat.prime_two.eq_one_or_self_of_dvd (orderOf t)
      (orderOf_dvd_of_pow_eq_one (elemPow_eq_one_of_isElementaryAbelian t ht))).resolve_left
      (fun ho => ht1 (orderOf_eq_one_iff.mp ho))
  refine ⟨t, ht, ht2, ?_⟩
  intro hzt
  exact htF (subset_closure ⟨ht.1, hzt⟩)

/-- Application to the literal selected intersection, keeping the conjugator. -/
public theorem SelectedFusionData.exists_second_involution (h : Hypotheses z)
    (d : FusionEightData z) (a : SelectedFusionData h) :
    ∃ t : G, t ∈ coreIntersection z a.g ∧ orderOf t = 2 ∧ ¬ IsConj z t :=
  exists_second_involution_of_intersection d a.g a.intersection_elementary
    a.intersection_card a.intersection_ne_fusion

/-- The two actual centralizer isomorphisms give the required centralizer
orders; Thompson's formula supplies the ambient order without simplicity. -/
public theorem SecondCentralizerAlternative.order_cases (h : Hypotheses z)
    {t : G} (ht : orderOf t = 2) (hnt : ¬ IsConj z t)
    (c : LocalInvolutionCensus z t) (b : SecondCentralizerAlternative z t) :
    Nat.card G = 12096 ∨ Nat.card G = 95040 := by
  have ho := card_eq z t h.involution ht hnt c.classes
  change Nat.card G = kappa z t z * Nat.card (Centralizer t) +
    kappa z t t * Nat.card (Centralizer z) at ho
  rw [c.count_at_z, h.centralizer_card] at ho
  rcases b with ⟨⟨e⟩, hb⟩ | ⟨⟨e⟩, hb⟩
  · left
    have hc : Nat.card (Centralizer t) = 48 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card]
      norm_num [Fintype.card_perm]
    simpa only [hc, hb] using ho
  · right
    have hc : Nat.card (Centralizer t) = 240 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card]
      norm_num [Fintype.card_perm]
    simpa only [hc, hb] using ho

/-- Assemble every field of the published geometry once the three independent
local source arguments have been supplied. None of these premises includes
the ambient order or the desired action. -/
public theorem nonempty_sourceGeometry_of_local_inputs (h : Hypotheses z)
    (d : FusionEightData z) (a : SelectedFusionData h)
    (hc : ∀ t : G, t ∈ coreIntersection z a.g → orderOf t = 2 → ¬ IsConj z t →
      LocalInvolutionCensus z t)
    (hb : ∀ t : G, t ∈ coreIntersection z a.g → orderOf t = 2 → ¬ IsConj z t →
      (∀ x : G, orderOf x = 2 → IsConj z x ∨ IsConj t x) →
      SecondCentralizerAlternative z t) : Nonempty (SourceGeometry h) := by
  obtain ⟨t, htE, ht, hnt⟩ := a.exists_second_involution h d
  have c := hc t htE ht hnt
  have b := hb t htE ht hnt c.classes
  exact ⟨{
    g := a.g
    fused_mem := a.fused_mem
    fused_ne := a.fused_ne
    intersection_elementary := a.intersection_elementary
    intersection_card := a.intersection_card
    intersection_ne_fusion := a.intersection_ne_fusion
    u := a.u
    u_order := a.u_order
    u_centralizes := a.u_centralizes
    u_conjugate_core := a.u_conjugate_core
    u_not_core := a.u_not_core
    u_fused := a.u_fused
    u_inverts_X := a.u_inverts_X
    t := t
    t_mem := htE
    t_order := ht
    t_not_fused := hnt
    involution_classes := c.classes
    order_cases := b.order_cases h ht hnt c }⟩

/-- The local assembly feeds the existing action construction on the actual
cosets of the eleven-point subgroup. The subgroup construction is independent. -/
public theorem nonempty_action_of_local_inputs (h : Hypotheses z)
    (d : FusionEightData z) (a : SelectedFusionData h)
    (hc : ∀ t : G, t ∈ coreIntersection z a.g → orderOf t = 2 → ¬ IsConj z t →
      LocalInvolutionCensus z t)
    (hb : ∀ t : G, t ∈ coreIntersection z a.g → orderOf t = 2 → ¬ IsConj z t →
      (∀ x : G, orderOf x = 2 → IsConj z x ∨ IsConj t x) →
      SecondCentralizerAlternative z t)
    (b : ElevenSubgroupData z) : Nonempty (DegreeTwelveAction G) := by
  obtain ⟨s⟩ := nonempty_sourceGeometry_of_local_inputs h d a hc hb
  exact nonempty_action_of_sourceGeometry h s b

/--
The complete nonnormal-fusion local geometry.  The selected intersection is
constructed first; its first projection supplies the core containment needed by
the census, while the census classes are exactly the fusion input required by
the second-centralizer recognition.  The resulting order alternatives and all
other fields are then assembled by `nonempty_sourceGeometry_of_local_inputs`.
-/
public theorem nonempty_sourceGeometry
    (h : Hypotheses z) (hn : QuaternionSubgroupsNormal z)
    (d : FusionEightData z) (hnon : ¬ (fusionCore z).Normal) :
    Nonempty (SourceGeometry h) := by
  obtain ⟨a⟩ := nonempty_selectedFusionData h hn d hnon
  apply nonempty_sourceGeometry_of_local_inputs h d a
  · intro t htE ht hnt
    exact Census.localInvolutionCensus_of_quaternion_normal h hn d a htE.1 ht hnt
  · intro t htE ht hnt hclasses
    exact secondCentralizerAlternative h hn d a t htE ht hnt hclasses

/-- Named source-facing alias for the nonnormal fusion branch. -/
public theorem nonempty_sourceGeometry_of_nonnormal_fusion
    (h : Hypotheses z) (hn : QuaternionSubgroupsNormal z)
    (d : FusionEightData z) (hnon : ¬ (fusionCore z).Normal) :
    Nonempty (SourceGeometry h) :=
  nonempty_sourceGeometry h hn d hnon

end CFSG.Quasithin.Extraspecial32.DegreeTwelve
