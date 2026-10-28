module
public import Theory.Representation.BinaryAlternatingSevenCubicRecognition
public import Theory.Representation.NormalElementaryQuotient
public import Theory.GroupTheory.CoprimeSubgroupCentralizer

/-!
# Commuting involutions for cubics in exceptional A₇ extensions

A cubic with a nonzero fixed vector on the elementary sixteen-group
centralizes an involution in that core. Otherwise its faithful action is
fixed-point-free, so its quotient image is a three-cycle in A₇. That image
centralizes a four-group on the unused letters. Coprime centralizer lifting
then makes the actual cubic centralizer even, and Cauchy's theorem gives
an involution in the extension itself. No complement is assumed.

This proves the exceptional-local calculation in Aschbacher–Smith 5.2.14(2),
printed p.654 (`refs/quasithin.pdf`); the source consumer supplies ambient
fusion via 5.2.14(1).
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace Theory.GroupTheory.QuasithinM23

/-- Every cubic in an exceptional elementary-sixteen A₇ extension centralizes
an actual involution in that extension. -/
theorem exceptional_cubic_centralizes_involution
    {X : Type*} [Group X] [Finite X]
    (U : Subgroup X) [U.Normal] [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 16)
    (q : X →* alternatingGroup (Fin 7)) (hq : Function.Surjective q)
    (hk : q.ker = U) (hC : centralizer (U : Set X) = U)
    (c : X) (hc : orderOf c = 3) : ∃ z : X, orderOf z = 2 ∧ Commute c z := by
  classical
  let ρ := NormalElementaryQuotient.representation U q hq (hk.trans hC.symm)
  have hf := NormalElementaryQuotient.representation_injective U q hq (hk.trans hC.symm)
  have hd : Module.finrank (ZMod 2) (Additive U) = 4 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    calc
      2 ^ Module.finrank (ZMod 2) (Additive U) = Nat.card (Additive U) := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
      _ = 2^4 := (Nat.card_congr Additive.toMul).trans hU
  have hqc : orderOf (q c) = 3 := by
    apply orderOf_eq_prime
    · simpa only [hc,map_pow,map_one] using congrArg q (pow_orderOf_eq_one c)
    · intro hz
      have hcu : c ∈ U := hk ▸ (show c ∈ q.ker from hz)
      have hh := orderOf_dvd_of_pow_eq_one (elemPow_eq_one_of_isElementaryAbelian (p := 2) c hcu)
      rw [hc] at hh
      norm_num at hh
  by_cases he : ∃ v : Additive U, v ≠ 0 ∧ ρ (q c) v = v
  · obtain ⟨v,hv,hfix⟩ := he
    have hv1 : (v.toMul : X) ≠ 1 := by
      intro hh
      apply hv
      exact Additive.toMul.injective (Subtype.ext hh)
    refine ⟨v.toMul,orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ v.toMul.property) hv1,?_⟩
    have hh := congrArg (fun w : Additive U => (w.toMul : X)) hfix
    rw [NormalElementaryQuotient.representation_apply] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · have hfree (v : Additive U) (hv : ρ (q c) v = v) : v = 0 := by
      by_contra hv0
      exact he ⟨v,hv0,hv⟩
    have hthree := binaryAlternatingSeven_threeCycle_of_fixedPointFree ρ hf hd (q c) hqc hfree
    obtain ⟨b,_,hb2,_,hb1,_,_,hcb,_⟩ :=
      alternatingGroup.threeCycle_exists_commuting_involutions (q c) hthree
    have hb : orderOf b = 2 := orderOf_eq_prime hb2 hb1
    have hcp : IsPGroup 3 (zpowers c) := IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers,hc]; norm_num)
    have hmap := map_centralizer_eq_of_isPGroup_of_surjective_coprime 3 (zpowers c) hcp q hq
      (by rw [hk,hU]; decide)
    rw [MonoidHom.map_zpowers] at hmap
    simp only [zpowers_eq_closure,centralizer_closure] at hmap
    have hbC : b ∈ centralizer ({q c} : Set _) :=
      mem_centralizer_singleton_iff.mpr hcb.eq.symm
    have hd2 : 2 ∣ Nat.card (centralizer ({q c} : Set (alternatingGroup (Fin 7)))) := by
      have hh := orderOf_dvd_natCard (⟨b,hbC⟩ : centralizer ({q c} : Set _))
      rwa [←Subgroup.orderOf_coe,hb] at hh
    have hd2' : 2 ∣ Nat.card (centralizer ({c} : Set X)) := by
      rw [←hmap] at hd2
      exact hd2.trans (card_map_dvd _ _)
    obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' 2 hd2'
    refine ⟨z,(Subgroup.orderOf_coe z).trans hz,?_⟩
    exact (mem_centralizer_singleton_iff.mp z.property).symm

end Theory.GroupTheory.QuasithinM23
