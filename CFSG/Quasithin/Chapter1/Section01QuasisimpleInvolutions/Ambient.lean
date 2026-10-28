module

public import CFSG.Quasithin.Chapter1.Section01Inheritance
public import Theory.GroupTheory.SelfCentralizingCore
public import Mathlib.GroupTheory.FixedPointFree

/-!
# The ambient characteristic-two and inversion steps of 1.1.5

For the literal `Lemma115Hypotheses K S M z`, the intersection `K ∩ M`
has characteristic two by 1.1.4(4). The intersection of the odd core of K
with M is a normal odd subgroup of this characteristic-two group and is
therefore trivial. Since the centralizer of z lies in M, conjugation by z
on the odd core is fixed-point free; its square is the identity, so it is
inversion. The centralizer of z inside K also inherits characteristic two
from `K ∩ M`, providing the ambient input for the component argument.

All conclusions use the original element, subgroup inclusions and intrinsic
cores. Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 1.1.5(1–2) and the opening of (3), printed pp.501–502, combined
manuscript of 1 March 2004.
-/

namespace CFSG.Quasithin.Chapter1.Lemma115Hypotheses
open Subgroup
variable {G : Type*} [Group G]
variable {K M : Subgroup G} {S : Sylow 2 K} {z : G}

/-- The marked involution belongs to the actual intersection. -/
public theorem mem_intersection (h : Lemma115Hypotheses K S M z) : z ∈ K ⊓ M :=
  ⟨map_subtype_le _ h.mem_sylow, h.mem_HeOver.2.2 h.mem_sylow⟩

variable [Finite G]

/-- Lemma 1.1.5(1), in the ambient subgroup convention of Chapter 1. -/
public theorem intersection_mem_He (h : Lemma115Hypotheses K S M z) : K ⊓ M ∈ He G := by
  have hne : K ⊓ M ≠ ⊥ := by
    intro he
    have hz : z = 1 := mem_bot.mp (he ▸ mem_intersection h)
    have hh := h.involution
    rw [hz, orderOf_one] at hh
    omega
  exact lemma_1_1_4_4 hne inf_le_right h.mem_HeOver.1
    (le_inf h.core_centralizer_le (inf_le_left.trans (pCoreIn_le 2 M)))

/-- The same characteristic-two conclusion on the literal subgroup `M.subgroupOf K`. -/
public theorem intersection_characteristicTwo (h : Lemma115Hypotheses K S M z) :
    HasCharacteristicTwo (M.subgroupOf K) := by
  have hc : HasCharacteristicTwo (K ⊓ M : Subgroup G) := mem_He_iff.mp (intersection_mem_He h)
  have hh := hc.of_equiv (subgroupOfEquivOfLe (H := K ⊓ M) inf_le_left).symm
  exact hh.of_equiv (MulEquiv.subgroupCongr (inf_subgroupOf_left M K))

/-- The actual odd core of K meets M trivially. -/
public theorem oddCore_intersection_eq_bot (h : Lemma115Hypotheses K S M z) :
    (pPrimeCore 2 K).subgroupOf (M.subgroupOf K) = ⊥ := by
  let N := M.subgroupOf K
  let R := pPrimeCore 2 K
  have hcop : Nat.Coprime 2 (Nat.card (R.subgroupOf N)) := by
    rw [← inf_subgroupOf_right R N,
      Nat.card_congr (subgroupOfEquivOfLe (H := R ⊓ N) inf_le_right).toEquiv]
    exact pPrimeCore_coprime_card.of_dvd_right (card_dvd_of_le inf_le_left)
  have hle : R.subgroupOf N ≤ pPrimeCore 2 N := le_sSup ⟨inferInstance, hcop⟩
  rw [Theory.GroupTheory.pPrimeCore_eq_bot_of_centralizer_pCore_le 2
    (intersection_characteristicTwo h)] at hle
  exact le_bot_iff.mp hle

/-- Lemma 1.1.5(2): the original involution inverts the actual odd core of K. -/
public theorem inverts_oddCore (h : Lemma115Hypotheses K S M z)
    (r : K) (hr : r ∈ pPrimeCore 2 K) : z * (r : G) * z⁻¹ = (r : G)⁻¹ := by
  let zK : K := ⟨z, (mem_intersection h).1⟩
  let R := pPrimeCore 2 K
  let φ : MulAut R := MulAut.conjNormal zK
  have hz2 : zK ^ 2 = 1 := by
    apply Subtype.ext
    change z ^ 2 = 1
    rw [← h.involution]
    exact pow_orderOf_eq_one z
  have hinvol : Function.Involutive φ := by
    intro r
    change (((MulAut.conjNormal : K →* MulAut R) zK) *
      ((MulAut.conjNormal : K →* MulAut R) zK)) r = r
    rw [← map_mul, ← pow_two, hz2, map_one]
    rfl
  have hfree : MonoidHom.FixedPointFree φ := by
    intro r hr
    have he : z * ((r : K) : G) * z⁻¹ = ((r : K) : G) :=
      congrArg (fun t : R => ((t : K) : G)) hr
    have hrM : ((r : K) : G) ∈ M := h.centralizer_le
      (mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he).symm)
    have hm : (⟨r, hrM⟩ : M.subgroupOf K) ∈ R.subgroupOf (M.subgroupOf K) := r.property
    rw [oddCore_intersection_eq_bot h] at hm
    have hr1 : (r : K) = 1 := congrArg Subtype.val (mem_bot.mp hm)
    exact Subtype.ext hr1
  exact congrArg (fun t : R => ((t : K) : G))
    (congrFun (hfree.coe_eq_inv_of_involutive hinvol) ⟨r, hr⟩)

/-- The literal centralizer inside K inherits characteristic two, as used in 1.1.5(3). -/
public theorem centralizer_mem_He (h : Lemma115Hypotheses K S M z) :
    K ⊓ centralizer ({z} : Set G) ∈ He G := by
  have hp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by
    simpa only [Nat.card_zpowers, pow_one] using h.involution)
  have hh := pCoreIn_selfCentralizing_centralizer (intersection_mem_He h) hp
    (zpowers_le.mpr (mem_intersection h))
  have hc : centralizer (zpowers z : Set G) = centralizer ({z} : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  have he : (K ⊓ M) ⊓ centralizer ({z} : Set G) =
      K ⊓ centralizer ({z} : Set G) := by
    rw [inf_assoc, inf_eq_right.mpr h.centralizer_le]
  change (K ⊓ centralizer ({z} : Set G)) ⊓
    centralizer ((K ⊓ centralizer ({z} : Set G)).pCoreIn 2 : Set G) ≤ _
  simpa only [hc, he] using hh

/-- Intrinsic characteristic two for the actual ambient intersection centralizer. -/
public theorem centralizer_characteristicTwo (h : Lemma115Hypotheses K S M z) :
    HasCharacteristicTwo (K ⊓ centralizer ({z} : Set G) : Subgroup G) :=
  mem_He_iff.mp h.centralizer_mem_He

/-- Characteristic two in the intrinsic centralizer of the marked element of K. -/
public theorem intrinsic_centralizer_characteristicTwo (h : Lemma115Hypotheses K S M z) :
    HasCharacteristicTwo (centralizer ({(⟨z, h.mem_intersection.1⟩ : K)} : Set K)) := by
  let C := K ⊓ centralizer ({z} : Set G)
  let D := centralizer ({(⟨z, h.mem_intersection.1⟩ : K)} : Set K)
  let e : C ≃* D :=
    { toFun := fun x => ⟨⟨x, x.property.1⟩,
        mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp x.property.2))⟩
      invFun := fun x => ⟨x, x.val.property,
        mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  exact h.centralizer_characteristicTwo.of_equiv e

/-- The ambient source conclusions feeding the marked component argument of 1.1.5. -/
public theorem ambient_conclusions (h : Lemma115Hypotheses K S M z) :
    K ⊓ M ∈ He G ∧ HasCharacteristicTwo (M.subgroupOf K) ∧
      (∀ r : K, r ∈ pPrimeCore 2 K → z * (r : G) * z⁻¹ = (r : G)⁻¹) ∧
      K ⊓ centralizer ({z} : Set G) ∈ He G :=
  ⟨h.intersection_mem_He, h.intersection_characteristicTwo,
    h.inverts_oddCore, h.centralizer_mem_He⟩

end CFSG.Quasithin.Chapter1.Lemma115Hypotheses
