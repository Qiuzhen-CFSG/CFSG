module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.Borel

/-!
# The prime support of the marked Cartan

The preceding split-torus marking identifies X with two copies of the
defining field's units. Hence its prime support lies in q−1. The already
proved coprimality of Y with q−1 therefore implies coprimality with X,
and odd field degree excludes the prime three from X.

The marking is explicit earlier geometry, to be supplied by the original
flag/Cartan producer. Arbitrary `Geometry` data do not have this property.
Source: Aschbacher--Smith 11.5.6(3), printed p.781.
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Exact order from the preceding full split-Cartan marking. -/
theorem cartan_card_of_split_marking
    (e : E.X ≃* (E.input.field.Carrierˣ × E.input.field.Carrierˣ)) :
    Nat.card E.X = (2 ^ E.input.field.degree - 1) ^ 2 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_units,
    E.input.field.card_eq, pow_two]

/-- The marked Cartan has no prime outside q−1. -/
theorem cartan_prime_support_of_split_marking
    (e : E.X ≃* (E.input.field.Carrierˣ × E.input.field.Carrierˣ))
    {p : ℕ} (hp : p.Prime) (hd : p ∣ Nat.card E.X) :
    p ∣ 2 ^ E.input.field.degree - 1 := by
  rw [E.cartan_card_of_split_marking e] at hd
  exact hp.dvd_of_dvd_pow hd

/-- The source coprimality applies to the actual entire Cartan. -/
theorem cartan_coprime_Y_of_split_marking
    (e : E.X ≃* (E.input.field.Carrierˣ × E.input.field.Carrierˣ))
    (hc : Nat.Coprime (Nat.card E.Y) (2 ^ E.input.field.degree - 1)) :
    Nat.Coprime (Nat.card E.X) (Nat.card E.Y) := by
  rw [E.cartan_card_of_split_marking e]
  exact hc.symm.pow_left 2

/-- The literal component inherits the coprimality needed by the sieve. -/
theorem cartan_coprime_component_of_split_marking
    (e : E.X ≃* (E.input.field.Carrierˣ × E.input.field.Carrierˣ))
    (hc : Nat.Coprime (Nat.card E.Y) (2 ^ E.input.field.degree - 1))
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I) :
    Nat.Coprime (Nat.card E.X) (Nat.card I) :=
  (E.cartan_coprime_Y_of_split_marking e hc).of_dvd_right (card_dvd_of_le hI.1)

/-- The odd-degree A.3.15 application really has a three-prime actor. -/
theorem three_not_dvd_cartan_of_split_marking
    (e : E.X ≃* (E.input.field.Carrierˣ × E.input.field.Carrierˣ))
    (hn : Odd E.input.field.degree) : ¬ 3 ∣ Nat.card E.X := by
  rw [E.cartan_card_of_split_marking e]
  exact Nat.prime_three.coprime_iff_not_dvd.mp
    ((Nat.BinaryTorusParity.coprime_three_sub_one hn).pow_right 2)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
