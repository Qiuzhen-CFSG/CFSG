module
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.Transport

/-!
# Odd prime divisors across the two component quotients

For a quasisimple source component, (E1) makes the center a two-group.
The actual map from a subgroup to its central image therefore has a
two-group kernel. Its order formula shows that odd prime divisors survive.
The quotient by O² is also a two-group, so the same fact applies to residuals.

Apply these two facts to the containment of the outer residual in the inner
residual. This yields a comparison of their model fixed-subgroup orders even
when the central kernels of L and L′ differ. The model-specific applications
must supply numerical facts from genuine fixed-subgroup tables.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
16.1.2, 16.1.5, and the proof of 16.4.11(2), printed pp.1170–1172 and 1193.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The central-image map has a two-group kernel in the source component. -/
theorem centralImageMap_two_kernel {L X : Subgroup G} [IsQuasisimple L]
    (hodd : pPrimeCore 2 L = ⊥) (hXL : X ≤ L) :
    IsPGroup 2 (centralImageMap hXL).ker := by
  let f := centralImageMap hXL
  let j : f.ker →* center L :=
    ((inclusion hXL).comp f.ker.subtype).codRestrict (center L) (by
      intro x
      change (⟨x.val.val, hXL x.val.property⟩ : L) ∈ center L
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (center L) ⟨x.val.val, hXL x.val.property⟩ = 1
      have he := congrArg Subtype.val x.property
      simpa only [f, centralImageMap, MonoidHom.coe_mk, OneHom.coe_mk,
        Subgroup.coe_one] using he)
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : center L => (v.val.val : G)) he
  have hZ : IsPGroup 2 (center L) := by
    rw [IsQuasisimple.center_eq_pCore hodd]
    exact pCore_isPGroup
  exact hZ.of_injective j hj

/-- Odd prime divisors cannot disappear through either covering kernel. -/
theorem odd_prime_dvd_centralImage_iff {L X : Subgroup G} [IsQuasisimple L]
    (hodd : pPrimeCore 2 L = ⊥) (hXL : X ≤ L)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    q ∣ Nat.card (centralImage L X) ↔ q ∣ Nat.card X := by
  let f := centralImageMap hXL
  have hf := centralImageMap_surjective hXL
  constructor
  · exact fun h => h.trans (Subgroup.card_dvd_of_surjective f hf)
  · intro h
    have hc : Nat.card f.ker * Nat.card (centralImage L X) = Nat.card X := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
      exact f.ker.card_mul_index
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (centralImageMap_two_kernel hodd hXL)
    have hqn : ¬ q ∣ Nat.card f.ker := by
      rw [hn]
      intro hd
      have hqdiv := hq.dvd_of_dvd_pow hd
      exact hq2 ((Nat.dvd_prime Nat.prime_two).mp hqdiv |>.resolve_left hq.ne_one)
    exact (hq.dvd_mul.mp (hc ▸ h)).resolve_left hqn

/-- Passing to O² preserves the odd prime divisors of a finite group. -/
theorem odd_prime_dvd_residual_iff {H : Type*} [Group H] [Finite H]
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    q ∣ Nat.card (pResidual 2 H) ↔ q ∣ Nat.card H := by
  constructor
  · exact fun h => h.trans (card_subgroup_dvd_card _)
  · intro h
    have hc := (pResidual 2 H).card_mul_index
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (isPGroup_quotient_pResidual (G := H) 2)
    have hqn : ¬ q ∣ (pResidual 2 H).index := by
      rw [index_eq_card, hn]
      intro hd
      exact hq2 ((Nat.dvd_prime Nat.prime_two).mp
        (hq.dvd_of_dvd_pow hd) |>.resolve_left hq.ne_one)
    exact (hq.dvd_mul.mp (hc ▸ h)).resolve_right hqn

variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- Residual containment transports every odd prime divisor of the outer
 central image into the inner image, without identifying the two centers. -/
theorem outer_odd_prime_dvd_inner (d : Contrary T z L g R r)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hout : q ∣ Nat.card (centralImage (L.conjBy g) (residual (L.conjBy g) z))) :
    q ∣ Nat.card (centralImage L (residual L r)) := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  let : IsQuasisimple (L.conjBy g) :=
    IsQuasisimple.of_mulEquiv ((MulAut.conj g).subgroupMap L)
  have houter := (odd_prime_dvd_centralImage_iff (conjugate_oddCore d)
    ((residual_le (L.conjBy g) z).trans inf_le_left) hq hq2).mp hout
  exact (odd_prime_dvd_centralImage_iff (component_oddCore d)
    ((residual_le L r).trans inf_le_left) hq hq2).mpr
      (houter.trans (Subgroup.card_dvd_of_le d.residual_normal.1))

/-- A prime present in every outer fixed row and absent in every inner
 fixed row excludes the model. Model-specific applications must derive
 these numerical facts from the actual table extensions or isomorphisms. -/
theorem not_quotient_model_of_odd_prime_fixed_rows (d : Contrary T z L g R r)
    {S : Type*} [Group S] [Finite S] (e : (L ⧸ center L) ≃* S)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hin : ∀ a : MulAut S, orderOf a = 2 → (∃ x, a = MulAut.conj x) →
      ¬ q ∣ Nat.card a.fixedSubgroup)
    (hout : ∀ a : MulAut S, orderOf a = 2 → (¬ ∃ x, a = MulAut.conj x) →
      q ∣ Nat.card a.fixedSubgroup) : False := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  let ec : L ≃* L.conjBy g := (MulAut.conj g).subgroupMap L
  let : IsQuasisimple (L.conjBy g) := IsQuasisimple.of_mulEquiv ec
  let eM := (centralQuotientCongr ec).symm.trans e
  let hi := d.setup.sylow_normalizes (d.setup.le_sylow d.mem)
  let a := MulAut.centralQuotientAction e (action hi)
  let b := MulAut.centralQuotientAction eM (action d.z_normalizes)
  have ha : orderOf a = 2 :=
    (orderOf_injective (MulAut.centralQuotientAction e)
      (MulAut.centralQuotientAction_injective e) _).trans d.inner_action_order
  have hb : orderOf b = 2 :=
    (orderOf_injective (MulAut.centralQuotientAction eM)
      (MulAut.centralQuotientAction_injective eM) _).trans d.outer_action_order
  have hia : ∃ x : S, a = MulAut.conj x :=
    (MulAut.centralQuotientAction_inner_iff e (action hi)).mpr d.inner_action
  have hob : ¬ ∃ x : S, b = MulAut.conj x := fun h =>
    d.outer_action ((MulAut.centralQuotientAction_inner_iff eM _).mp h)
  have hbo := (odd_prime_dvd_residual_iff hq hq2).mpr (hout b hb hob)
  have ho : q ∣ Nat.card (centralImage (L.conjBy g) (residual (L.conjBy g) z)) := by
    rw [Nat.card_congr (centralImageModelEquiv (conjugate_oddCore d) eM
      d.z_normalizes).toEquiv]
    exact hbo
  have hai := outer_odd_prime_dvd_inner d hq hq2 ho
  rw [Nat.card_congr (centralImageModelEquiv (component_oddCore d) e hi).toEquiv] at hai
  exact hin a ha hia ((odd_prime_dvd_residual_iff hq hq2).mp hai)
end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies
