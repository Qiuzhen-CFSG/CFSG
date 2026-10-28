module

public import CFSG.Quasithin.Chapter14.Section01.SourcePreliminaries.Calculations
public import Theory.GroupTheory.Commutator.NormalClosure

/-!
# Quotient data for the residual splitting

Write `D` for the intersection core inside `M`, `Q` for `O₂(M)`, and `f`
for the action map onto S₃. The equality `D ∩ ker(f) = Q` makes `D/Q`
embed into its nontrivial two-subgroup image in S₃, so `D/Q` has order two.
The commutator bound descends to commutation with the star action kernel.
Normality of the centralizer propagates this bound to the normal closure
of `D` and hence to its two-residual.

These are the algebraic inputs from 14.1.17 and the R₂ condition, before
any direct-product or residual identification is made.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), printed pp.980–981, Lemmas 14.1.17–18.
-/

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter14.SourcePreliminaries

private theorem two_image_card
    {H : Type*} [Group H] (f : H →* Equiv.Perm (Fin 3))
    (D : Subgroup H) (hD : IsPGroup 2 D) (hne : ¬ D ≤ f.ker) :
    Nat.card (D.map f) = 2 := by
  have hcard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hd : Nat.card (D.map f) ∣ 6 := hcard ▸ (D.map f).card_subgroup_dvd_card
  have hcop : Nat.Coprime (Nat.card (D.map f)) 3 := by
    obtain ⟨n, hn⟩ := (hD.map f).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have hd2 : Nat.card (D.map f) ∣ 2 := hcop.dvd_mul_right.mp hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with hc | hc
  · exact (hne ((map_eq_bot_iff D).mp (card_eq_one.mp hc))).elim
  · exact hc

/-- The intersection-centralizer equality produces the actual star reflection. -/
public theorem quotient_reflection_data
    {H : Type*} [Group H] [Finite H]
    (f : H →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (D Q : Subgroup H) [Q.Normal] (hQker : Q ≤ f.ker)
    (hD : IsPGroup 2 D) (hne : ¬ D ≤ f.ker)
    (hmeet : D ⊓ f.ker = Q) (hcomm : ⁅f.ker, D⁆ ≤ Q) :
    let q := QuotientGroup.mk' Q
    let fstar := QuotientGroup.lift Q f hQker
    Function.Surjective fstar ∧
    ∃ w : H ⧸ Q, D.map q = zpowers w ∧ orderOf w = 2 ∧ fstar w ≠ 1 ∧
      ∀ k ∈ fstar.ker, w * k = k * w := by
  let q := QuotientGroup.mk' Q
  let fstar := QuotientGroup.lift Q f hQker
  let Dstar := D.map q
  have hcomp : fstar.comp q = f := QuotientGroup.lift_comp_mk' Q f hQker
  have hmap : Dstar.map fstar = D.map f := by
    rw [map_map, hcomp]
  have hinj : Function.Injective (fstar.domRestrict Dstar) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨d, hd, hdq⟩ := x.property
    have hdf : f d = 1 := by
      change fstar (x : H ⧸ Q) = 1 at hx
      rw [← hdq] at hx
      exact hx
    have hdQ : d ∈ Q := hmeet ▸ (show d ∈ D ⊓ f.ker from ⟨hd, hdf⟩)
    apply Subtype.ext
    exact hdq.symm.trans ((QuotientGroup.eq_one_iff d).mpr hdQ)
  have hcard : Nat.card Dstar = 2 := by
    have he := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [MonoidHom.domRestrict_range, hmap, two_image_card f D hD hne] at he
    exact he
  obtain ⟨w, hwne, hall⟩ := (Nat.card_eq_two_iff' (1 : Dstar)).mp hcard
  have hw : orderOf w = 2 := by
    have hd : orderOf w ∣ 2 := hcard ▸ orderOf_dvd_natCard w
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact (hwne (orderOf_eq_one_iff.mp h)).elim
    · exact h
  have hwval : orderOf (w : H ⧸ Q) = 2 := by
    exact (orderOf_injective Dstar.subtype Dstar.subtype_injective w).trans hw
  have hzp : Dstar = zpowers (w : H ⧸ Q) := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr w.property) ?_).symm
    rw [Nat.card_zpowers, hwval, hcard]
  have hfw : fstar (w : H ⧸ Q) ≠ 1 := by
    intro h
    apply hwne
    apply hinj
    simpa using h
  have hcommstar : ⁅fstar.ker, Dstar⁆ = ⊥ := by
    rw [QuotientGroup.ker_lift, ← map_commutator, Subgroup.map_eq_bot_iff]
    simpa only [QuotientGroup.ker_mk'] using hcomm
  have hcent : fstar.ker ≤ centralizer (Dstar : Set (H ⧸ Q)) :=
    commutator_eq_bot_iff_le_centralizer.mp hcommstar
  refine ⟨?_, w, hzp, hwval, hfw, ?_⟩
  · intro t
    obtain ⟨x, rfl⟩ := hf t
    exact ⟨q x, rfl⟩
  · intro k hk
    exact mem_centralizer_iff.mp (hcent hk) w w.property

/-- A commutator bound propagates from a subgroup to its normal-closure residual. -/
public theorem residual_normalClosure_commutator_le
    {H : Type*} [Group H] (C D Q : Subgroup H) [C.Normal] [Q.Normal]
    (hcomm : ⁅C, D⁆ ≤ Q) :
    ⁅C, twoResidualAmbient (normalClosure (D : Set H))⁆ ≤ Q := by
  exact (commutator_mono le_rfl (map_subtype_le _)).trans
    (commutator_normalClosure_le_of_normal C D Q hcomm)
end CFSG.Quasithin.Chapter14.SourcePreliminaries
