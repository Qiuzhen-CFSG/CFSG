module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Held.Reduction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ChiZeroQuotient
public import CFSG.Quasithin.ChapterC.Section01.SolvableShortAbelianCore.QuotientThree

/-!
# Excluding chi-zero blocks from a native Held subgroup calculation

The second Held local normalizes the join of the two normal elementary
order-64 subgroups; it is not one of the individual E64 normalizers.
Its required subnormal calculation allows quotient orders three and nine,
with groups in the cubic branch larger than twelve. This native calculation
is an explicit premise here, not a consequence of the geometry.

A chi-zero block has simple two-core quotient. A nontrivial coordinate image
therefore has the same two-core quotient via an actual quotient isomorphism.
Order nine is excluded by the concrete block models; a cubic quotient forces
the original short group to have order twelve, too small to surject onto the
native cubic branch. All coordinates vanish, forcing the block to be central,
contrary to its nonzero commutator module. This uses orders only to exclude
models, never to recognize groups or representations.

Source: Aschbacher–Smith 2.3.9(7), printed p.526, and C.1.7–13, pp.123–125;
GLS3 Table 5.3p. Final assembly must discharge the native calculation.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.HeldCase
open Subgroup ChapterC Theory.GroupTheory

/-- Nine is not the order of any of the actual chi-zero acting quotients. -/
theorem not_chiZero_of_quotient_card_nine {B : Type*} [Group B]
    (hq : Nat.card (B ⧸ pCore 2 B) = 9) : ¬ IsChiZeroBlock B := by
  intro h
  rcases LieType.chiZero_order_module h with ⟨n, hn, he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
  · have hl : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
    have hr : 2 ^ 4 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by decide) (by omega)
    have hp := Nat.mul_le_mul hl (Nat.sub_le_sub_right hr 1)
    rw [← he, hq] at hp
    norm_num at hp
  · omega
  · omega

private theorem core_quotient_card_of_simple {B E : Type*} [Group B] [Group E] [Finite B]
    [IsSimpleGroup (B ⧸ pCore 2 B)] (f : B →* E) (hf : Function.Surjective f)
    (hne : 1 < Nat.card (E ⧸ pCore 2 E)) :
    Nat.card (B ⧸ pCore 2 B) = Nat.card (E ⧸ pCore 2 E) := by
  let : Finite E := Finite.of_surjective f hf
  have hm : (pCore 2 B).map f ≤ pCore 2 E :=
    le_sSup ⟨Normal.map inferInstance f hf, pCore_isPGroup.map f⟩
  let t := (QuotientGroup.mk' (pCore 2 E)).comp f
  have hk : pCore 2 B ≤ t.ker := by
    intro b hb
    exact (QuotientGroup.eq_one_iff _).mpr (hm ⟨b, hb, rfl⟩)
  let q := QuotientGroup.lift (pCore 2 B) t hk
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 E) y
    obtain ⟨b, rfl⟩ := hf e
    exact ⟨QuotientGroup.mk' (pCore 2 B) b, rfl⟩
  let : Nontrivial (E ⧸ pCore 2 E) := Finite.one_lt_card_iff_nontrivial.mp hne
  have hi : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff q).mp
    rcases (inferInstance : q.ker.Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · have hqone := MonoidHom.ker_eq_top_iff.mp ht
      obtain ⟨y, hy⟩ := exists_ne (1 : E ⧸ pCore 2 E)
      obtain ⟨b, rfl⟩ := hq y
      exact (hy (DFunLike.congr_fun hqone b)).elim
  exact Nat.card_congr (MulEquiv.ofBijective q ⟨hi, hq⟩).toEquiv

/-- Required native subnormal calculation for the Held seed normalizer.
This is a sufficient finite calculation, not its proof. -/
def SubnormalLargeLocalOrders (P : Type*) [Group P] : Prop :=
  ∀ E : Subgroup P, E.IsSubnormal → IsPPerfect 2 E →
    Nat.card E = 1 ∨
      (Nat.card (E ⧸ pCore 2 E) = 3 ∧ 12 < Nat.card E) ∨
        Nat.card (E ⧸ pCore 2 E) = 9

/-- The native subnormal restrictions exclude every chi-zero block with
central-kernel, subnormal coordinates in a power of that native group. -/
theorem not_chiZero_of_central_power_large_orders {B P : Type*} [Group B] [Group P]
    (hB : IsChiZeroBlock B) (hP : SubnormalLargeLocalOrders P) {n : ℕ}
    (q : B →* (Fin n → P)) (hqc : q.ker ≤ center B) (hqs : q.range.IsSubnormal) : False := by
  have hs := hB.chi.short
  let := hs.finite
  let := hB.quotient_simple
  have hzero (b : B) (i : Fin n) : q b i = 1 := by
    let ev := Pi.evalMonoidHom (fun _ : Fin n => P) i
    have hev : Function.Surjective ev := fun p => ⟨fun _ => p, rfl⟩
    let f := ev.comp q
    have hfsub : f.range.IsSubnormal := by
      rw [MonoidHom.range_comp]
      exact hqs.map hev
    have hfp : IsPPerfect 2 f.range := hs.twoPerfect.of_surjective
      f.rangeRestrict f.rangeRestrict_surjective
    rcases hP f.range hfsub hfp with h1 | ⟨h3, hlarge⟩ | h9
    · have hz : f.range = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      exact DFunLike.congr_fun (MonoidHom.range_eq_bot_iff.mp hz) b
    · have hqcard := core_quotient_card_of_simple f.rangeRestrict
        f.rangeRestrict_surjective (by rw [h3]; decide)
      have hBcard : Nat.card B = 12 := hs.card_eq_twelve_of_quotient_three (hqcard.trans h3)
      have hc := Nat.card_le_card_of_surjective f.rangeRestrict f.rangeRestrict_surjective
      rw [hBcard] at hc
      omega
    · have hqcard := core_quotient_card_of_simple f.rangeRestrict
        f.rangeRestrict_surjective (by rw [h9]; decide)
      exact (not_chiZero_of_quotient_card_nine (hqcard.trans h9) hB).elim
  have hcenter : (⊤ : Subgroup B) ≤ center B := by
    intro b _
    exact hqc (funext (hzero b))
  apply hs.blockU_ne_bot
  exact commutator_top_right_eq_bot_iff_le_center.mpr ((le_top : pCore 2 B ≤ ⊤).trans hcenter)

end CFSG.Quasithin.Chapter2.ComponentRefinement.HeldCase

end
