module
public import Theory.GroupTheory.ElementarySixtyFourThreeRank
public import Theory.GroupTheory.ElementarySixtyFourPrimeCores
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.Representation.BinaryGroupAction
import Mathlib.Tactic

/-!
# Three-rank in a faithful binary six-space

The ambient binary automorphism order has three-part 3^4. A faithful
binary six-space excludes an elementary actor of order 81, so every
three-rank witness has rank at most three. This retains the given
representation and requires no irreducibility or subgroup recognition.

Source application: Aschbacher--Smith G.9.4, printed p.355.
-/

open Subgroup
namespace Representation.BinarySixThreeRank

/-- A faithful binary action of degree at most six has three-rank at most three. -/
public theorem primeRank_three_le_three
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V ≤ 6) : primeRank 3 G ≤ 3 := by
  let Vmul := Multiplicative V
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 Vmul := BinaryGroupAction.elementary
  have hcard : Nat.card Vmul ≤ 64 := by
    change Nat.card V ≤ 64
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hd
  let := BinaryGroupAction.action ρ
  let f : G →* MulAut Vmul := MulDistribMulAction.toMulAut G Vmul
  have hf' : Function.Injective f := by
    intro g k he
    apply hf
    ext v
    exact congrArg Multiplicative.toAdd
      (MulEquiv.congr_fun he (Multiplicative.ofAdd v))
  apply (primeRank_le_iff_elementary_card_le G).mpr
  intro E hE
  let : IsElementaryAbelian 3 E := hE
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 3 E).exists_card_eq
  have hdvd : 3 ^ n ∣ 20158709760 := by
    rw [← hn]
    exact (card_dvd_of_injective (f.comp E.subtype) (hf'.comp E.subtype_injective)).trans
      (card_mulAut_dvd_of_elementary_card_le_sixtyfour hcard)
  have hnle : n ≤ 4 := by
    by_contra hh
    have hbad : 3 ^ 5 ∣ 20158709760 :=
      (pow_dvd_pow 3 (by omega : 5 ≤ n)).trans hdvd
    norm_num at hbad
  have hn4 : n ≠ 4 := by
    intro h4
    have hEcard : Nat.card (E.map f) = 81 := by
      rw [card_map_of_injective hf',hn,h4]
      decide
    let : IsElementaryAbelian 3 (E.map f) := IsElementaryAbelian.map (A := E) f
    exact not_card_eightyone_elementary_three_subgroup_binary_le_sixtyfour
      hcard (E.map f) hEcard
  rw [hn]
  have hlt : n ≤ 3 := by omega
  exact Nat.pow_le_pow_right (by decide : 0 < 3) hlt

end Representation.BinarySixThreeRank

