module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection
public import Theory.GroupAction.AutomorphismFixedTransport
/-!
# Transport and order obstructions for the sporadic inspection

Both A₇ and its perfect central triple cover have order divisible by 2520.
Thus a group whose order is not divisible by 2520 contains neither. The same
argument applies to the common fixed subgroup of an entire two-subgroup of
automorphisms: if that actor is nontrivial, Cauchy's theorem supplies one of
its involutions, and the common fixed subgroup lies in that involution's
fixed subgroup. No transfer of component membership to this larger fixed
subgroup is asserted or needed for the order obstruction.

The isomorphism transport separately preserves the actual actor, fixed subgroup,
embedded component and intrinsic component membership.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), inspection in
E.6.18, printed p.252; Theorem C, printed p.33.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
namespace SporadicInspection
variable {G H : Type*} [Group G] [Group H]

/-- The ordinary and triple-cover seven models both contribute a factor 2520. -/
theorem seven_card_dvd {L : Subgroup G} (hL : IsSeven L) : 2520 ∣ Nat.card L := by
  have hA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup]
    norm_num
  rcases hL with ha | hc
  · obtain ⟨e⟩ := ha
    rw [Nat.card_congr e.toEquiv, hA]
  · obtain ⟨_, _, ⟨e⟩⟩ := hc
    have hd := (center L).card_quotient_dvd_card
    rwa [Nat.card_congr e.toEquiv, hA] at hd

/-- An order obstruction excludes even the existence of an embedded seven subgroup. -/
theorem of_card (hG : ¬ 2520 ∣ Nat.card G) : SevenActionInspection G := by
  intro P _ L _ _ hL
  exact (hG (seven_card_dvd hL |>.trans L.card_subgroup_dvd_card)).elim

/-- Involution fixed-subgroup orders control the common fixed subgroup of any two-group. -/
theorem of_involution_fixed_card [Finite G]
    (hc : ∀ r : MulAut G, orderOf r = 2 → ¬ 2520 ∣ Nat.card r.fixedSubgroup) :
    SevenActionInspection G := by
  intro P hp L hLF _ hL
  by_contra hn
  obtain ⟨a, ha, hane⟩ := P.bot_or_exists_ne_one.resolve_left hn
  have hne : (⟨a, ha⟩ : P) ≠ 1 := fun h => hane (congrArg Subtype.val h)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := P) 2
    ((hp.dvd_orderOf hne).trans (orderOf_dvd_natCard (x := (⟨a, ha⟩ : P))))
  have ht' : orderOf (t : MulAut G) = 2 := (Subgroup.orderOf_coe t).trans ht
  have hLt : L ≤ (t : MulAut G).fixedSubgroup := by
    intro x hx
    exact (MulAut.mem_fixedSubgroup _ _).mpr (hLF hx t)
  exact hc t ht' ((seven_card_dvd hL).trans (card_dvd_of_le hLt))

/-- Transport the full inspection through an actual multiplicative equivalence. -/
theorem of_equiv (e : G ≃* H) (hi : SevenActionInspection H) : SevenActionInspection G := by
  intro P hp L hLF hL hs
  let R := P.map (MulAut.congr e).toMonoidHom
  let F := FixedPoints.subgroup P G
  let D := FixedPoints.subgroup R H
  have fixed_iff (x : G) : e x ∈ D ↔ x ∈ F := by
    constructor
    · intro hx a
      apply e.injective
      change e (a.val x) = e x
      have he := hx ⟨MulAut.congr e a, mem_map_of_mem _ a.property⟩
      change e (a.val (e.symm (e x))) = e x at he
      simpa only [e.symm_apply_apply] using he
    · intro hx r
      obtain ⟨a, ha, he⟩ := r.property
      change r.val (e x) = e x
      rw [← he]
      change e (a (e.symm (e x))) = e x
      rw [e.symm_apply_apply]
      exact congrArg e (hx ⟨a, ha⟩)
  let f : F ≃* D :=
    { toFun := fun x => ⟨e x, (fixed_iff x).mpr x.property⟩
      invFun := fun y => ⟨e.symm y, (fixed_iff (e.symm y)).mp (by
        simpa only [e.apply_symm_apply] using y.property)⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y)
      map_mul' := fun x y => Subtype.ext (e.map_mul x y) }
  let J := L.map e.toMonoidHom
  have hJD : J ≤ D := by
    rintro _ ⟨x, hx, rfl⟩
    exact (fixed_iff x).mpr (hLF hx)
  have heq : (L.subgroupOf F).map f.toMonoidHom = J.subgroupOf D := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_map_of_mem e.toMonoidHom hx
    · intro hy
      obtain ⟨x, hx, he⟩ := hy
      have hxF : x ∈ F := hLF hx
      exact ⟨⟨x, hxF⟩, hx, Subtype.ext he⟩
  have hR : R = ⊥ := hi R (hp.map _) J hJD
    (heq ▸ hL.map_equiv f) (hs.of_equiv (e.subgroupMap L))
  apply bot_unique
  intro a ha
  have he : MulAut.congr e a = 1 := by
    have hm : MulAut.congr e a ∈ R := mem_map_of_mem _ ha
    simpa only [hR, mem_bot] using hm
  exact mem_bot.mpr ((MulAut.congr e).injective (he.trans (map_one _).symm))
end SporadicInspection
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
