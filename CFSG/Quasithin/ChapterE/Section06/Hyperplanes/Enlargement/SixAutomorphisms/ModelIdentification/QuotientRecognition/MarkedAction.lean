module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Action
/-!
# The literal actor image in the fixed-six quotient action

Retain the entire original V-action as well as its distinguished cyclic
A-action when transporting the component and its Sylow through the central
quotient. This strengthened constructor makes later selected actors actual
images of the original source action.

Source: Aschbacher–Smith E.6.23, printed p.254 (PDF p.265).
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo
variable {G : Type*} [Group G] [Finite G] {M V U A L X Y : Subgroup G} {g : G}
theorem quotient_fixed_six_action_marked [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) :
    ∃ s : FixedSixAction (Y ⧸ center Y),
      s.actors = (actionImage V Y).map (quotientAut (center Y)) ∧
      zpowers s.involution = (actionImage A Y).map (quotientAut (center Y)) := by
  let _ := extension_quasisimple hY
  let q := QuotientGroup.mk' (center Y)
  let S := X.subgroupOf Y
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := actionImage A Y) 2
    (by rw [action_order_two d hY])
  have hz : zpowers (b : MulAut Y) = actionImage A Y := by
    apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr b.property)
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hb, action_order_two d hY]
  have hfixed : FixedPoints.subgroup (actionImage A Y) Y = (b : MulAut Y).fixedSubgroup := by
    ext x
    constructor
    · intro hx
      exact (MulAut.mem_fixedSubgroup _ _).mpr (hx b)
    · intro hx
      have hle : zpowers b.val ≤ MulAction.stabilizer (MulAut Y) x :=
        zpowers_le.mpr ((MulAut.mem_fixedSubgroup _ _).mp hx)
      intro a
      exact hle (hz.symm ▸ a.property)
  have hS : IsComponentIn S (b : MulAut Y).fixedSubgroup := by
    rw [← hfixed]
    exact ⟨(six_fixed_component d hY).1, (six_fixed_component d hY).2.1⟩
  have hqinj : Function.Injective (q.subgroupMap S) := by
    intro x y hh
    apply (subgroupOfEquivOfLe hY.proper.le).injective
    apply six_quotient_embedding_injective d hY
    exact congrArg Subtype.val hh
  let e : X ≃* S.map q := (subgroupOfEquivOfLe hY.proper.le).symm.trans
    (MulEquiv.ofBijective (q.subgroupMap S) ⟨hqinj, q.subgroupMap_surjective S⟩)
  obtain ⟨e₆⟩ := d.six.model
  have hm : Nonempty (S.map q ≃* alternatingGroup (Fin 6)) := ⟨e.symm.trans e₆⟩
  have hne : S.map q ≠ ⊥ := by
    have hc : Nat.card (S.map q) = 360 := by
      rw [Nat.card_congr (e.symm.trans e₆).toEquiv, nat_card_alternatingGroup]
      norm_num
    intro hh
    rw [hh, Nat.card_unique] at hc
    contradiction
  have hAV : actionImage A Y ≤ actionImage V Y :=
    Subgroup.map_mono (fun _ hx => d.subspace_mem.1 hx)
  obtain ⟨P, _, hP⟩ := whole_action_fixes_component_sylow h d hY
  refine ⟨{
    actors := (actionImage V Y).map (quotientAut (center Y))
    elementary := quotient_action_elementary d hY
    card_actors := quotient_whole_action_order d hY
    involution := quotientAut (center Y) b.val
    involution_mem := mem_map_of_mem _ (hAV b.property)
    involution_order := ?_
    six := S.map q
    component := ?_
    model := hm
    sylow := P.mapSurjective (f := e.toMonoidHom) e.surjective
    fixes := ?_ }, rfl, ?_⟩
  · rw [orderOf_injective _ MulAut.quotient_center_injective, Subgroup.orderOf_coe, hb]
  · exact IsComponentIn.map_fixed_of_central_ker b.val _ q
      (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
      (fun x => (quotientAut_apply_mk (center Y) b.val x).symm) hS hne
  · rintro a ⟨c, hc, rfl⟩ x hx
    change x ∈ (P : Subgroup X).map e.toMonoidHom at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change quotientAut (center Y) c (q (inclusion hY.proper.le y)) =
      q (inclusion hY.proper.le y)
    rw [quotientAut_apply_mk, hP c hc y hy]
  · change zpowers (quotientAut (center Y) b.val) = _
    rw [← MonoidHom.map_zpowers, hz]

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo
