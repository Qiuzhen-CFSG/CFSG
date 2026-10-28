module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.OddCore.FiveCentralizer.Setup
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.OddCore.FiveCentralizer.CoreCalculation
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
public import Theory.GroupTheory.InvolutionFusionFromCentralizer
import Mathlib.GroupTheory.Perm.Centralizer

/-!
# Held's five-element centralizer: the intersection and involution fusion

Let w have order five in the supplied A₆. The subgroup A₆⟨μ′⟩ ≃ S₆ normalizes
the marked four-group V. Their product covers C_G(μ); their orders
4 and 720, and the given centralizer order 2880, make multiplication bijective.
An order-five permutation of six points is a five-cycle with centralizer its
own cyclic group. Since w centralizes V, restriction of the multiplication map
therefore identifies C_G(μ) ∩ C_G(w) with V × ⟨w⟩.

This proves order twenty and exponent ten for the internal centralizer of μ.
Its only involutions are μ, λ and μλ, cycled by uv. The general Sylow-center
fusion lemma then proves conjugacy of all involutions inside C_G(w).
The order-twenty calculation also discharges the existing odd-core reduction.
No root identification or odd-core conclusion is assumed.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 5.3, printed p.236.
-/

open Subgroup Equiv
noncomputable section

namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.OddCore.FiveCentralizer

theorem symmetric_six_five_centralizer (w : Perm (Fin 6)) (hw : orderOf w = 5) :
    centralizer ({w} : Set (Perm (Fin 6))) = zpowers w := by
  have hc : w.IsCycle := Perm.isCycle_of_prime_order' (hw ▸ (by decide : Nat.Prime 5))
    (by simp [hw])
  have hcard : Nat.card (centralizer ({w} : Set (Perm (Fin 6)))) = 5 := by
    rw [Perm.nat_card_centralizer, hc.cycleType, ← hc.orderOf, hw]
    norm_num
  apply (eq_of_le_of_card_ge (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)) ?_).symm
  rw [Nat.card_zpowers, hw, hcard]

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (L : Source.SixLocalData D e)

abbrev four : Subgroup G := closure ({mu D e, lam D e} : Set G)
abbrev six : Subgroup G := L.A ⊔ zpowers (mu' D e)

theorem four_mem (x : G) : x ∈ four D e ↔
    x = 1 ∨ x = mu D e ∨ x = lam D e ∨ x = mu D e * lam D e :=
  mem_closure_pair_iff _ _ (by simpa [pow_two] using element_square D e 1 (by decide))
    (by simpa [pow_two] using element_square D e 6 (by decide)) (mu_commute_lam D e) x

theorem four_klein : IsKleinFour (four D e) := by
  apply isKleinFour_closure_pair _ _
    (by simpa [pow_two] using element_square D e 1 (by decide))
    (by simpa [pow_two] using element_square D e 6 (by decide))
    (element_ne_one D e 1) (element_ne_one D e 6) ?_ (mu_commute_lam D e)
  intro h
  have hh : modelElement 1 = modelElement 6 := D.a10ModelEmbedding_injective e h
  exact (by decide +kernel : modelElement 1 ≠ modelElement 6) hh

theorem four_card : Nat.card (four D e) = 4 := (four_klein D e).card_four

theorem four_square (x : four D e) : x ^ 2 = 1 := by
  apply Subtype.ext
  change x.val ^ 2 = 1
  rcases (four_mem D e x.val).mp x.property with h | h | h | h
  · simp [h]
  · rw [h]; exact element_square D e 1 (by decide)
  · rw [h]; exact element_square D e 6 (by decide)
  · rw [h, (mu_commute_lam D e).mul_pow, element_square D e 1 (by decide),
      element_square D e 6 (by decide), one_mul]

theorem A_commute_four (a : L.A) (v : four D e) : Commute (a : G) (v : G) := by
  have hm : Commute (a : G) (mu D e) :=
    (mem_centralizer_iff.mp (L.A_centralizes a.property) _ (by simp)).symm
  have hl : Commute (a : G) (lam D e) :=
    (mem_centralizer_iff.mp (L.A_centralizes a.property) _ (by simp)).symm
  rcases (four_mem D e v.val).mp v.property with h | h | h | h
  · rw [h]; exact Commute.one_right _
  · exact h ▸ hm
  · exact h ▸ hl
  · exact h ▸ hm.mul_right hl

theorem six_normalizes_four : six D e L ≤ normalizer (four D e) := by
  apply sup_le
  · exact L.A_centralizes.trans ((by rw [centralizer_closure] :
      centralizer ({mu D e, lam D e} : Set G) ≤ centralizer (four D e)).trans
      (centralizer_le_normalizer _))
  · apply zpowers_le.mpr
    have hi : (mu' D e)⁻¹ = mu' D e :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using element_square D e 2 (by decide))
    have hl : mu' D e * lam D e * mu' D e = mu D e * lam D e := by
      have h : modelElement 2 * modelElement 6 * modelElement 2 =
          modelElement 1 * modelElement 6 := by decide +kernel
      simpa only [mu', lam, mu, element, map_mul] using congrArg (D.a10ModelEmbedding e) h
    have hm : mu' D e * mu D e * (mu' D e)⁻¹ = mu D e := by
      rw [(mu_commute_mu' D e).symm.eq, mul_inv_cancel_right]
    have hc (v : G) (hv : v ∈ four D e) :
        mu' D e * v * (mu' D e)⁻¹ ∈ four D e := by
      rcases (four_mem D e v).mp hv with rfl | rfl | rfl | rfl
      · simp
      · rw [hm]; exact subset_closure (by simp)
      · rw [hi, hl]; exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
      · have : mu' D e * (mu D e * lam D e) * (mu' D e)⁻¹ =
            (mu' D e * mu D e * (mu' D e)⁻¹) *
            (mu' D e * lam D e * (mu' D e)⁻¹) := by group
        rw [this, hm, hi, hl]
        exact mul_mem (subset_closure (by simp))
          (mul_mem (subset_closure (by simp)) (subset_closure (by simp)))
    rw [mem_normalizer_iff]
    intro v
    constructor
    · exact hc v
    · intro hv
      have hh := hc _ hv
      have he : mu' D e * (mu' D e * v * (mu' D e)⁻¹) * (mu' D e)⁻¹ = v := by
        rw [hi]
        calc
          _ = (mu' D e * mu' D e) * v * (mu' D e * mu' D e) := by group
          _ = v := by
            rw [← pow_two, element_square D e 2 (by decide), one_mul, mul_one]
      rwa [he] at hh

theorem centralizer_eq_four_sup_six :
    centralizer ({mu D e} : Set G) = four D e ⊔ six D e L := by
  simpa only [sup_assoc] using L.centralizer_mu

def centralizerProduct : four D e × six D e L → centralizer ({mu D e} : Set G) :=
  fun x => ⟨x.1 * x.2, by
    rw [centralizer_eq_four_sup_six D e L]
    exact mul_mem_sup x.1.property x.2.property⟩

theorem centralizerProduct_surjective : Function.Surjective (centralizerProduct D e L) := by
  intro x
  have hx : x.val ∈ four D e ⊔ six D e L := by
    rw [← centralizer_eq_four_sup_six D e L]; exact x.property
  change x.val ∈ (↑(four D e ⊔ six D e L) : Set G) at hx
  rw [coe_mul_of_right_le_normalizer_left _ _ (six_normalizes_four D e L)] at hx
  obtain ⟨a, ha, b, hb, hab⟩ := hx
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩

theorem centralizerProduct_bijective [Finite G]
    (hcentralizer : Nat.card (centralizer ({D.a10NoncentralInvolution e} : Set G)) = 2880) :
    Function.Bijective (centralizerProduct D e L) := by
  apply (centralizerProduct_surjective D e L).bijective_of_nat_card_le
  rw [Nat.card_prod, four_card, Nat.card_congr L.symmetricEquiv.toEquiv, Nat.card_perm,
    Nat.card_fin, mu_eq, hcentralizer]
  norm_num [Nat.factorial]

variable (w : G) (hwA : w ∈ L.A)

include hwA

theorem cyclic_commute_four (a : four D e) (b : zpowers w) :
    Commute (a : G) (b : G) := by
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp b.property
  rw [← hn]
  exact (A_commute_four D e L ⟨w, hwA⟩ a).symm.zpow_right n

theorem six_commuting_mem_zpowers (hw : orderOf w = 5) (s : six D e L)
    (hs : Commute (s : G) w) : (s : G) ∈ zpowers w := by
  let wS : six D e L := ⟨w, (show L.A ≤ six D e L from le_sup_left) hwA⟩
  have hwS : orderOf (L.symmetricEquiv wS) = 5 := by
    rw [MulEquiv.orderOf_eq, ← orderOf_coe]
    exact hw
  have hc : L.symmetricEquiv s ∈ centralizer ({L.symmetricEquiv wS} : Set (Perm (Fin 6))) :=
    mem_centralizer_singleton_iff.mpr
      ((show Commute s wS from Subtype.ext hs.eq).map L.symmetricEquiv).eq
  rw [symmetric_six_five_centralizer _ hwS] at hc
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hc
  have he : wS ^ n = s := L.symmetricEquiv.injective (by simpa only [map_zpow] using hn)
  exact mem_zpowers_iff.mpr ⟨n, congrArg Subtype.val he⟩

def intersectionProduct : four D e × zpowers w →*
    (centralizer ({mu D e} : Set G) ⊓ ambient w : Subgroup G) :=
  ((four D e).subtype.noncommCoprod (zpowers w).subtype
    (cyclic_commute_four D e L w hwA)).codRestrict _ (by
      intro x
      change (x.1 : G) * (x.2 : G) ∈ _
      have hb : (x.2 : G) ∈ L.A := zpowers_le.mpr hwA x.2.property
      refine ⟨?_, ?_⟩
      · rw [centralizer_eq_four_sup_six D e L]
        exact mul_mem_sup x.1.property ((show L.A ≤ six D e L from le_sup_left) hb)
      · apply mem_centralizer_singleton_iff.mpr
        have hbw : Commute (x.2 : G) w := by
          obtain ⟨n, hn⟩ := mem_zpowers_iff.mp x.2.property
          rw [← hn]
          exact (Commute.refl w).zpow_left n
        exact ((A_commute_four D e L ⟨w, hwA⟩ x.1).symm.mul_left hbw).eq)

theorem intersectionProduct_surjective (hw : orderOf w = 5) :
    Function.Surjective (intersectionProduct D e L w hwA) := by
  intro x
  obtain ⟨⟨v, s⟩, hs⟩ := centralizerProduct_surjective D e L ⟨x.val, x.property.1⟩
  have hx : (v : G) * (s : G) = x.val := congrArg Subtype.val hs
  have hsw : Commute (s : G) w := by
    have hxw : x.val * w = w * x.val := mem_centralizer_singleton_iff.mp x.property.2
    change (s : G) * w = w * (s : G)
    apply mul_left_cancel (a := (v : G))
    calc
      _ = x.val * w := by rw [← mul_assoc, hx]
      _ = w * x.val := hxw
      _ = _ := by rw [← hx, ← mul_assoc, (A_commute_four D e L ⟨w, hwA⟩ v).eq, mul_assoc]
  exact ⟨(v, ⟨s.val, six_commuting_mem_zpowers D e L w hwA hw s hsw⟩), Subtype.ext hx⟩

theorem intersectionProduct_injective [Finite G]
    (hcentralizer : Nat.card (centralizer ({D.a10NoncentralInvolution e} : Set G)) = 2880) :
    Function.Injective (intersectionProduct D e L w hwA) := by
  intro x y hxy
  let xs : six D e L := ⟨x.2.val, (show L.A ≤ six D e L from le_sup_left)
    (zpowers_le.mpr hwA x.2.property)⟩
  let ys : six D e L := ⟨y.2.val, (show L.A ≤ six D e L from le_sup_left)
    (zpowers_le.mpr hwA y.2.property)⟩
  have he : centralizerProduct D e L (x.1, xs) = centralizerProduct D e L (y.1, ys) := by
    apply Subtype.ext
    exact congrArg (fun z : (centralizer ({mu D e} : Set G) ⊓ ambient w : Subgroup G) => (z : G)) hxy
  have hh := (centralizerProduct_bijective D e L hcentralizer).injective he
  apply Prod.ext
  · exact congrArg (fun p : four D e × six D e L => p.1) hh
  · exact Subtype.ext (congrArg (fun p : four D e × six D e L => p.2.val) hh)

/-- The full intersection is the direct product of the marked four-group and ⟨w⟩. -/
public def intersectionEquiv [Finite G]
    (hcentralizer : Nat.card (centralizer ({D.a10NoncentralInvolution e} : Set G)) = 2880)
    (hw : orderOf w = 5) : closure ({mu D e, lam D e} : Set G) × zpowers w ≃*
      (centralizer ({mu D e} : Set G) ⊓ ambient w : Subgroup G) :=
  MulEquiv.ofBijective (intersectionProduct D e L w hwA)
    ⟨intersectionProduct_injective D e L w hwA hcentralizer,
      intersectionProduct_surjective D e L w hwA hw⟩

variable [Finite G]
  (hcentralizer : Nat.card (centralizer ({D.a10NoncentralInvolution e} : Set G)) = 2880)
  (hw : orderOf w = 5)

include hcentralizer hw

/-- Held 5.3: the actual ambient centralizer intersection has order twenty. -/
public theorem intersection_card :
    Nat.card (centralizer ({mu D e} : Set G) ⊓ ambient w : Subgroup G) = 20 := by
  rw [← Nat.card_congr (intersectionEquiv D e L w hwA hcentralizer hw).toEquiv,
    Nat.card_prod, four_card, Nat.card_zpowers, hw]

def internalEquiv : four D e × zpowers w ≃*
    centralizer ({first D e L w hwA} : Set (ambient w)) :=
  (intersectionEquiv D e L w hwA hcentralizer hw).trans (firstCentralizerEquiv D e L w hwA).symm

/-- Every element of the involution centralizer inside C_G(w) has tenth power one. -/
public theorem firstCentralizer_pow_ten (x : centralizer ({first D e L w hwA} : Set (ambient w))) :
    x ^ 10 = 1 := by
  let E := internalEquiv D e L w hwA hcentralizer hw
  obtain ⟨y, rfl⟩ := E.surjective x
  rw [← map_pow, ← E.map_one]
  apply congrArg E
  apply Prod.ext
  · change y.1 ^ 10 = 1
    rw [show 10 = 2 * 5 from rfl, pow_mul, four_square, one_pow]
  · change y.2 ^ 10 = 1
    have h5 : y.2 ^ 5 = 1 := by
      have hh := pow_card_eq_one' (x := y.2)
      rwa [Nat.card_zpowers, hw] at hh
    rw [show 10 = 5 * 2 from rfl, pow_mul, h5, one_pow]

theorem centralizer_involution_mem_four (x : centralizer ({first D e L w hwA} : Set (ambient w)))
    (hx : orderOf (x : ambient w) = 2) :
    ((x : ambient w) : G) ∈ four D e := by
  let E := internalEquiv D e L w hwA hcentralizer hw
  obtain ⟨y, hy⟩ := E.surjective x
  have hy2 : y ^ 2 = 1 := by
    apply E.injective
    rw [map_pow, hy, map_one]
    apply Subtype.ext
    change (x : ambient w) ^ 2 = 1
    rw [← hx, pow_orderOf_eq_one]
  have hb2 : y.2 ^ 2 = 1 := congrArg (fun z : four D e × zpowers w => z.2) hy2
  have hb5 : orderOf y.2 ∣ 5 := by
    have hh := orderOf_dvd_natCard y.2
    rwa [Nat.card_zpowers, hw] at hh
  have hb : y.2 = 1 := orderOf_eq_one_iff.mp
    (Nat.dvd_one.mp (Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hb2) hb5))
  have hxy : ((x : ambient w) : G) = (y.1 : G) * (y.2 : G) :=
    (congrArg (fun z : centralizer ({first D e L w hwA} : Set (ambient w)) =>
      ((z : ambient w) : G)) hy).symm
  rw [hxy, hb, Subgroup.coe_one, mul_one]
  exact y.1.property

/-- All involutions of the actual five-centralizer are conjugate there to μ. -/
public theorem involution_isConj_first (x : ambient w) (hx : orderOf x = 2) :
    IsConj x (first D e L w hwA) := by
  apply Theory.GroupTheory.isConj_of_involution_of_centralizer_fusion
    (first_order D e L w hwA) ?_ hx
  intro y hy hyc
  let yc : centralizer ({first D e L w hwA} : Set (ambient w)) :=
    ⟨y, mem_centralizer_singleton_iff.mpr hyc.eq⟩
  have hm := centralizer_involution_mem_four D e L w hwA hcentralizer hw yc hy
  have h12 : IsConj (first D e L w hwA) (second D e L w hwA) :=
    isConj_iff.mpr ⟨(cycler D e L w hwA)⁻¹,
      by simpa only [inv_inv] using cycle_first D e L w hwA⟩
  have h23 : IsConj (second D e L w hwA)
      (first D e L w hwA * second D e L w hwA) :=
    isConj_iff.mpr ⟨(cycler D e L w hwA)⁻¹,
      by simpa only [inv_inv] using cycle_second D e L w hwA⟩
  rcases (four_mem D e y.val).mp hm with h | h | h | h
  · have hy1 : y = 1 := Subtype.ext h
    simp [hy1] at hy
  · have he : y = first D e L w hwA := Subtype.ext h
    exact he ▸ IsConj.refl _
  · have he : y = second D e L w hwA := Subtype.ext h
    exact he ▸ h12.symm
  · have he : y = first D e L w hwA * second D e L w hwA := Subtype.ext h
    exact he ▸ (h12.trans h23).symm

/-- The product identification is the literal ambient multiplication map. -/
public theorem intersectionEquiv_apply
    (x : closure ({mu D e, lam D e} : Set G) × zpowers w) :
    (intersectionEquiv D e L w hwA hcentralizer hw x : G) = (x.1 : G) * (x.2 : G) := by
  rfl

/-- The local intersection calculation discharges the Brauer–Wielandt input. -/
public theorem oddCore_card : Nat.card (pPrimeCore 2 (ambient w)) = 5 :=
  oddCore_card_of_intersection_card D e L w hwA hw
    (intersection_card D e L w hwA hcentralizer hw)

/-- The odd core is the literal central subgroup generated by the five-element. -/
public theorem oddCore_eq_kernel : pPrimeCore 2 (ambient w) = kernel w :=
  oddCore_eq_kernel_of_intersection_card D e L w hwA hw
    (intersection_card D e L w hwA hcentralizer hw)

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.OddCore.FiveCentralizer
