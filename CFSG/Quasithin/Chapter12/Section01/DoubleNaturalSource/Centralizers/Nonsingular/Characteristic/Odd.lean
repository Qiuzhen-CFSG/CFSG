module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.Moving
public import CFSG.Quasithin.Chapter1.Section01Inheritance
public import Theory.GroupTheory.SelfCentralizingCore

/-!
# Trivial odd core in the adapted nonsingular centralizer

Choose a nonidentity z on the original T-fixed line. Even characteristic
makes C_G(z) characteristic two, and centralizer inheritance does the same
for C_G(w,z). The moving-subgroup argument places O(C_G(w)) inside this
intersection. Its normality there and odd order force it to be trivial.

This discharges the odd-core paragraph of 12.1.1; ordinary components still
need to be excluded to obtain characteristic two for all of C_G(w).
Source: Aschbacher--Smith, 12.1.1, printed p.788.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- A nonsingular point of the original orbit is an involution. -/
theorem doubleNatural_point_orderOf_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ w : componentOrbit V (T : Subgroup G),
      B.quadratic (Additive.ofMul w) = 1 → orderOf (w : G) = 2 := by
  let := D.doubledOrbit_elementary h
  intro w hw
  apply orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (w : G) w.property)
  intro he
  have hew : w = 1 := Subtype.ext he
  rw [hew] at hw
  change B.quadratic 0 = 1 at hw
  exact zero_ne_one (by simpa only [QuadraticMap.map_zero] using hw)

/-- A nonidentity original T-fixed point has characteristic-two ambient centralizer. -/
theorem doubleNatural_fixedPoint_centralizer_characteristic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) (z : G)
    (hz : z ∈ B.fixedLine) (hz1 : z ≠ 1) :
    centralizer ({z} : Set G) ∈ Chapter1.He G := by
  let := D.doubledOrbit_elementary h
  have hz2 : orderOf z = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz.1) hz1
  exact Chapter1.twoLocal_mem_He_of_sylow_le T (h.simpleQTKE.evenCharacteristic T)
    (isTwoLocal_involution_centralizer hz2)
    (fun t ht => mem_centralizer_singleton_iff.mpr (hz.2 t ht))

/-- Characteristic two in the literal intersection C_G(w,z). -/
theorem doubleNatural_point_fixedPoint_characteristic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) (w : componentOrbit V (T : Subgroup G))
    (z : G) (hz : z ∈ B.fixedLine) (hz1 : z ≠ 1) :
    B.pointCentralizer w ⊓ centralizer ({z} : Set G) ∈ Chapter1.He G := by
  let := D.doubledOrbit_elementary h
  have hc := D.doubleNatural_fixedPoint_centralizer_characteristic h B z hz hz1
  have hp : IsPGroup 2 (zpowers (w : G)) := by
    let := IsElementaryAbelian.zpowers_of_pow_eq_one
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (w : G) w.property)
    exact IsElementaryAbelian.isPGroup 2 _
  have hwz : zpowers (w : G) ≤ centralizer ({z} : Set G) := by
    apply zpowers_le.mpr
    exact mem_centralizer_singleton_iff.mpr
      (hz.2 w ((D.doubledOrbit_E322 h).le_sylow w.property))
  have hh := pCoreIn_selfCentralizing_centralizer hc hp hwz
  change (B.pointCentralizer w ⊓ centralizer ({z} : Set G)) ⊓
    centralizer ((B.pointCentralizer w ⊓ centralizer ({z} : Set G)).pCoreIn 2 : Set G) ≤ _
  simpa only [DoubledBranch.pointCentralizer,zpowers_eq_closure,centralizer_closure,
    inf_comm (centralizer ({z} : Set G))] using hh

/-- The odd core of an adapted nonsingular ambient centralizer is trivial. -/
theorem doubleNatural_adapted_oddCore_eq_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G),
      B.AdaptedPoint S w → pPrimeCore 2 (B.pointCentralizer w) = ⊥ := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  have hline : B.fixedLine ≠ ⊥ := by
    intro he
    apply hw.residual_moves
    intro x hx y hy
    have hy1 : y = 1 := mem_bot.mp (he ▸ hy)
    simp [hy1]
  obtain ⟨z,hz,hz1⟩ := B.fixedLine.bot_or_exists_ne_one.resolve_left hline
  let H := B.pointCentralizer w
  let C := centralizer ({z} : Set G)
  let R := pPrimeCore 2 H
  have hw2 := D.doubleNatural_point_orderOf_two h B w hw.nonsingular
  have hsqt : IsStronglyQuasithin H :=
    (h.simpleQTKE.twoLocal_sqtk (isTwoLocal_involution_centralizer hw2)).stronglyQuasithin
  have hRC : R.map H.subtype ≤ C := by
    intro r hr
    apply mem_centralizer_singleton_iff.mpr
    exact ((S.adapted_fixedLine_centralizes_oddCore w hw hsqt) hz r hr)
  let K := C.subgroupOf H
  have hK : HasCharacteristicTwo K := by
    have hHC : HasCharacteristicTwo (H ⊓ C : Subgroup G) :=
      Chapter1.mem_He_iff.mp (D.doubleNatural_point_fixedPoint_characteristic h B w z hz hz1)
    have hh := hHC.of_equiv
      (subgroupOfEquivOfLe (H := H ⊓ C) inf_le_left).symm
    exact hh.of_equiv (MulEquiv.subgroupCongr (inf_subgroupOf_left C H))
  have hcop : Nat.Coprime 2 (Nat.card (R.subgroupOf K)) := by
    rw [← inf_subgroupOf_right R K,
      Nat.card_congr (subgroupOfEquivOfLe (H := R ⊓ K) inf_le_right).toEquiv]
    exact pPrimeCore_coprime_card.of_dvd_right (card_dvd_of_le inf_le_left)
  have hle : R.subgroupOf K ≤ pPrimeCore 2 K := le_sSup ⟨inferInstance,hcop⟩
  rw [pPrimeCore_eq_bot_of_centralizer_pCore_le 2 hK] at hle
  apply le_bot_iff.mp
  intro r hr
  have hrK : r ∈ K := hRC (mem_map_of_mem _ hr)
  have he := mem_bot.mp (hle (show (⟨r,hrK⟩ : K) ∈ R.subgroupOf K from hr))
  exact mem_bot.mpr (congrArg Subtype.val he)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
