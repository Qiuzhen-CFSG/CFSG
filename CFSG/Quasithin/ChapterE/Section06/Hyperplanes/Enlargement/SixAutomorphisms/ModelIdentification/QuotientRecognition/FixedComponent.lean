module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Action
public import Theory.GroupAction.CentralKernelFixedComponents

/-!
# The actual A₆ component survives the central quotient

Choose a generator of the order-two A-action. Its common fixed subgroup
is the fixed subgroup of this generator. Under a central quotient the
image of this fixed subgroup is normal in the full quotient fixed subgroup,
so its faithfully embedded A₆ component remains a component there.
Faithful automorphism descent also preserves the elementary order-eight
V-action. These statements retain actual maps and fixed subgroups.

Source: Aschbacher–Smith, E.6.23, printed p.254 (PDF p.265), combined
manuscript of 1 March 2004; the component transport is general finite-group
calculus, implemented in `Theory.GroupAction.CentralKernelFixedComponents`.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen
variable {G : Type*} [Group G] [Finite G] {M V U A L X Y : Subgroup G} {g : G}

/-- The actual image of X is an A₆ component of a quotient involution centralizer. -/
theorem quotient_fixed_six_component [IsElementaryAbelian 2 V]
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) :
    ∃ a : MulAut (Y ⧸ center Y), orderOf a = 2 ∧
      IsComponentIn ((X.subgroupOf Y).map (QuotientGroup.mk' (center Y))) a.fixedSubgroup ∧
      Nonempty (((X.subgroupOf Y).map (QuotientGroup.mk' (center Y))) ≃*
        alternatingGroup (Fin 6)) := by
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
  let e : S ≃* S.map q := MulEquiv.ofBijective (q.subgroupMap S)
    ⟨hqinj, q.subgroupMap_surjective S⟩
  obtain ⟨e₆⟩ := d.six.model
  have hm : Nonempty (S.map q ≃* alternatingGroup (Fin 6)) :=
    ⟨e.symm.trans ((subgroupOfEquivOfLe hY.proper.le).trans e₆)⟩
  have hne : S.map q ≠ ⊥ := by
    obtain ⟨c⟩ := hm
    have hc : Nat.card (S.map q) = 360 := by
      rw [Nat.card_congr c.toEquiv, nat_card_alternatingGroup]
      norm_num
    intro hh
    rw [hh, Nat.card_unique] at hc
    contradiction
  refine ⟨quotientAut (center Y) b.val, ?_, ?_, hm⟩
  · rw [orderOf_injective _ MulAut.quotient_center_injective, Subgroup.orderOf_coe, hb]
  · exact IsComponentIn.map_fixed_of_central_ker b.val _ q
      (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
      (fun x => (quotientAut_apply_mk (center Y) b.val x).symm) hS hne

omit [Finite G] in
/-- Perfectness preserves the order of every induced subgroup of automorphisms. -/
theorem quotient_action_card
    (hY : NormalComponentExtension U A X g Y) (D : Subgroup G) :
    Nat.card ((actionImage D Y).map (quotientAut (center Y))) = Nat.card (actionImage D Y) := by
  let _ := extension_quasisimple hY
  exact Subgroup.card_map_of_injective MulAut.quotient_center_injective

/-- The whole V-action retains order eight on Y/Z(Y). -/
theorem quotient_whole_action_order [IsElementaryAbelian 2 V]
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) :
    Nat.card ((actionImage V Y).map (quotientAut (center Y))) = 8 := by
  rw [quotient_action_card hY V, whole_action_order d hY]

omit [Finite G] in
/-- The descended V-action is elementary abelian, with its genuine action image. -/
theorem quotient_action_elementary [IsElementaryAbelian 2 V]
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) :
    IsElementaryAbelian 2 ((actionImage V Y).map (quotientAut (center Y))) := by
  let _ := IsElementaryAbelian.subgroupOf (p := 2)
    (hY.normalized_by_V d.subspace_mem.1)
  let _ : IsElementaryAbelian 2 (actionImage V Y) :=
    IsElementaryAbelian.map Y.normalizerMonoidHom
  exact IsElementaryAbelian.map (quotientAut (center Y))

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen
