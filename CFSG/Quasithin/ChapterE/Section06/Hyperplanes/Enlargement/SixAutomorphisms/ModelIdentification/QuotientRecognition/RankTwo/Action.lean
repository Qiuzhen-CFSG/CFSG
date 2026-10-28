module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Branches
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.FixedComponent
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Source

/-!
# The marked quotient action for the rank-two inspection

The quotient involution belongs to the actual elementary order-eight action.
The embedded A₆ is a component of its fixed subgroup, and the whole action
fixes a Sylow two-subgroup of that A₆ pointwise. Keeping these assertions
together permits the exceptional Sp₄(4) calculation to use the same involution,
component and Sylow subgroup. No Sylow assertion about C_G(A₁) is made.

Source: Aschbacher–Smith, E.6.23, printed p.254 (PDF p.265), together with
E.6.5 and E.6.8, printed pp.246–248, combined manuscript of 1 March 2004.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo

/-- The linked action data actually supplied by the source configuration.
This is an input to intrinsic model calculations, not a recognition theorem. -/
structure FixedSixAction (D : Type*) [Group D] where
  actors : Subgroup (MulAut D)
  elementary : IsElementaryAbelian 2 actors
  card_actors : Nat.card actors = 8
  involution : MulAut D
  involution_mem : involution ∈ actors
  involution_order : orderOf involution = 2
  six : Subgroup D
  component : IsComponentIn six involution.fixedSubgroup
  model : Nonempty (six ≃* alternatingGroup (Fin 6))
  sylow : Sylow 2 six
  fixes : ∀ a ∈ actors, ∀ x ∈ (sylow : Subgroup six), a (x : D) = x

/-- Transport all marked data by one genuine equivalence, including the
pointwise action on the chosen component Sylow subgroup. -/
@[expose] noncomputable def FixedSixAction.map {D E : Type*} [Group D] [Group E] [Finite D]
    (s : FixedSixAction D) (e : D ≃* E) : FixedSixAction E := by
  let t := MulAut.congr e
  let k := e.subgroupMap s.six
  have hfixed : s.involution.fixedSubgroup.map e.toMonoidHom =
      (t s.involution).fixedSubgroup := by
    ext x
    rw [mem_map_equiv, MulAut.mem_fixedSubgroup, MulAut.mem_fixedSubgroup]
    change s.involution (e.symm x) = e.symm x ↔ e (s.involution (e.symm x)) = x
    rw [← e.injective.eq_iff, e.apply_symm_apply]
  let _ := s.elementary
  refine {
    actors := s.actors.map t.toMonoidHom
    elementary := IsElementaryAbelian.map t.toMonoidHom
    card_actors := (Subgroup.card_map_of_injective t.injective).trans s.card_actors
    involution := t s.involution
    involution_mem := mem_map_of_mem _ s.involution_mem
    involution_order := (orderOf_injective t.toMonoidHom t.injective _).trans s.involution_order
    six := s.six.map e.toMonoidHom
    component := hfixed ▸ s.component.map e
    model := s.model.map (fun a => k.symm.trans a)
    sylow := s.sylow.mapSurjective (f := k.toMonoidHom) k.surjective
    fixes := ?_ }
  rintro a ⟨b, hb, rfl⟩ x hx
  change x ∈ (s.sylow : Subgroup s.six).map k.toMonoidHom at hx
  obtain ⟨y, hy, rfl⟩ := hx
  change e (b (e.symm (e y.val))) = e y.val
  rw [e.symm_apply_apply, s.fixes b hb y hy]

@[simp] theorem FixedSixAction.map_involution {D E : Type*} [Group D] [Group E] [Finite D]
    (s : FixedSixAction D) (e : D ≃* E) :
    (s.map e).involution = MulAut.congr e s.involution := rfl

variable {G : Type*} [Group G] [Finite G] {M V U A L X Y : Subgroup G} {g : G}

/-- Choose the quotient involution inside the actual V-action, preserving
the component and the pointwise fixed Sylow subgroup under the quotient map. -/
theorem quotient_fixed_six_action [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) :
    ∃ s : FixedSixAction (Y ⧸ center Y),
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
    fixes := ?_ }, ?_⟩
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
