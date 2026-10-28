module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FixedSpace.OddClasses.Contracts
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FixedSpace.OddClasses.Three.SeventhPower
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.PowerFusion.Three

/-!
# Two conjugacy classes cover the odd three-divisibility branch of HS

The checked cubic centralizer has order 360, and the explicit elementary
Sylow three-group excludes order nine. Thus every odd-order element whose
order is divisible by three has order three or fifteen. The cubic class
is already covered by the checked Sylow calculation.

For order fifteen, conjugate the fifth power to the marked cubic. Sylow-five
conjugacy inside its actual centralizer aligns the sixth power with a power
of the marked fifteen-element. The cubic component remains fixed, so the
original element is conjugate to a generator of that cyclic fifteen-group.
Square and seventh-power fusion cover all eight such generators.

The final theorem discharges the three-divisibility premise of
`oddClassBound_of_small_prime_covers`; no centralizer, order or fusion premise
remains. Every representative and conjugator belongs to the literal degree-100
carrier. Source: ATLAS HSG1-p100B0, classes 3A and 15A,
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/HS/.
-/

public section
namespace Sporadic.LeechRelated.HS.OddClassBound.Three
open ThreePowerFusion Subgroup

private theorem fifteen_power (k : ℕ) (hk : orderOf (fifteen ^ k) = 15) :
    IsConj fifteen (fifteen ^ k) := by
  have hmod (n : ℕ) : fifteen ^ (n % 15) = fifteen ^ n := by
    simpa only [fifteen_order] using pow_mod_orderOf fifteen n
  have hstep (n : ℕ) : IsConj (fifteen ^ n) (fifteen ^ ((2 * n) % 15)) := by
    rw [hmod]
    simpa only [← pow_mul] using fifteen_square.pow n
  have h4 : IsConj fifteen (fifteen ^ 4) := fifteen_square.trans (hstep 2)
  have h8 : IsConj fifteen (fifteen ^ 8) := h4.trans (hstep 4)
  have h14 : IsConj fifteen (fifteen ^ 14) := fifteen_seventh.trans (hstep 7)
  have h13 : IsConj fifteen (fifteen ^ 13) := h14.trans (hstep 14)
  have h11 : IsConj fifteen (fifteen ^ 11) := h13.trans (hstep 13)
  rw [← hmod k] at hk ⊢
  have hlt : k % 15 < 15 := Nat.mod_lt _ (by decide)
  interval_cases h : k % 15 <;> norm_num [orderOf_pow, fifteen_order] at hk
  · simpa using IsConj.refl fifteen
  · exact fifteen_square
  · exact h4
  · exact fifteen_seventh
  · exact h8
  · exact h11
  · exact h13
  · exact h14

private def fivePart : cubicCentralizer := ⟨fifteen ^ 6, by
  apply mem_centralizer_singleton_iff.mpr
  rw [← fifteen_fifth]
  exact ((Commute.refl fifteen).pow_pow 6 5).eq⟩

private theorem fivePart_order : orderOf fivePart = 5 := by
  rw [← orderOf_injective cubicCentralizer.subtype Subtype.val_injective fivePart]
  rw [show cubicCentralizer.subtype fivePart = fifteen ^ 6 from rfl]
  rw [orderOf_pow, fifteen_order]
  decide

private theorem centralizer_conjugate
    (d : Carrier) (hd : orderOf d = 15) (hd5 : d ^ 5 = cubic) : IsConj d fifteen := by
  let w : cubicCentralizer := ⟨d ^ 6, by
    apply mem_centralizer_singleton_iff.mpr
    rw [← hd5]
    exact ((Commute.refl d).pow_pow 6 5).eq⟩
  have hw : orderOf w = 5 := by
    rw [← orderOf_injective cubicCentralizer.subtype Subtype.val_injective w]
    change orderOf (d ^ 6) = 5
    rw [orderOf_pow, hd]
    decide
  have hsq : ¬ 5 ^ 2 ∣ Nat.card cubicCentralizer := by
    rw [cubicCentralizer_card]
    decide
  obtain ⟨k, c, hc⟩ := PrimeCyclicCoverage.exists_conjugate_pow_of_prime_sq_not_dvd
    (G := cubicCentralizer) (by decide : Nat.Prime 5) hsq fivePart_order hw
  have hc6 : (MulAut.conj (c : Carrier)) ((fifteen ^ 6) ^ k) = d ^ 6 := by
    exact (congrArg Subtype.val hc).symm
  have hcx : (MulAut.conj (c : Carrier)) cubic = cubic := by
    change (c : Carrier) * cubic * (c : Carrier)⁻¹ = cubic
    rw [mem_centralizer_singleton_iff.mp c.property, mul_assoc, mul_inv_cancel, mul_one]
  have hd16 : d ^ 16 = d := by
    rw [← pow_mod_orderOf, hd]
    simp
  have he : (MulAut.conj (c : Carrier)) (fifteen ^ (10 + 6 * k)) = d := by
    calc
      (MulAut.conj (c : Carrier)) (fifteen ^ (10 + 6 * k)) =
          (MulAut.conj (c : Carrier)) ((fifteen ^ 5) ^ 2 * (fifteen ^ 6) ^ k) := by
            rw [← pow_mul, ← pow_mul, ← pow_add]
      _ = cubic ^ 2 * d ^ 6 := by rw [map_mul, map_pow, fifteen_fifth, hcx, hc6]
      _ = d ^ 16 := by rw [← hd5, ← pow_mul, ← pow_add]
      _ = d := hd16
  have hconj : IsConj (fifteen ^ (10 + 6 * k)) d := isConj_iff.mpr ⟨c, he⟩
  have hp : orderOf (fifteen ^ (10 + 6 * k)) = 15 := by
    rw [← MulEquiv.orderOf_eq (MulAut.conj (c : Carrier)), he]
    exact hd
  exact hconj.symm.trans (fifteen_power _ hp).symm

/-- Every order-fifteen element lies in the chosen fifteen-element's class. -/
theorem orderFifteen_conjugate (g : Carrier) (hg : orderOf g = 15) : IsConj g fifteen := by
  have hg5 : orderOf (g ^ 5) = 3 := by
    rw [orderOf_pow, hg]
    decide
  obtain ⟨c, hc⟩ := isConj_iff.mp (cubic_class (g ^ 5) hg5).symm
  let d : Carrier := MulAut.conj c g
  have hd : orderOf d = 15 := (MulEquiv.orderOf_eq (MulAut.conj c) g).trans hg
  have hd5 : d ^ 5 = cubic := by
    change (MulAut.conj c g) ^ 5 = cubic
    rw [← map_pow]
    exact hc
  exact (isConj_iff.mpr ⟨c, rfl⟩).trans (centralizer_conjugate d hd hd5)

end Sporadic.LeechRelated.HS.OddClassBound.Three

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FixedSpace
open _root_.Sporadic.LeechRelated.HS.ThreePowerFusion

/-- The cubic and fifteen-element classes cover every odd-order HS element
whose order is divisible by three, including all mixed orders. -/
theorem oddThreeClassCover : OddThreeClassCover := by
  intro _hs
  refine ⟨![cubic, fifteen], ?_⟩
  intro g ho h3
  rcases odd_order_cases_of_cubicCentralizer_card cubicCentralizer_card_dvd g ho h3 with h | h
  · exact ⟨0, (cubic_class g h).symm⟩
  · exact ⟨1, _root_.Sporadic.LeechRelated.HS.OddClassBound.Three.orderFifteen_conjugate g h⟩

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FixedSpace
