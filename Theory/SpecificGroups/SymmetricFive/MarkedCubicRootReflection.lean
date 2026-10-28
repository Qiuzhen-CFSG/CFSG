module

public import Theory.SpecificGroups.SymmetricFive.ReflectionCommutator
import all Theory.SpecificGroups.SymmetricFive.ReflectionCommutator

/-!
# An inverted square root distinguishes a marked S5 reflection

An involutory automorphism acting like its fixed marked involution on a
cubic cannot have an even inner actor if it inverts a square root of that
marked involution. The ratio of two different even involutions would be
an even involution centralizing a cubic, impossible in S5. This avoids a
subgroup or automorphism enumeration and retains both marked elements.
-/

public noncomputable section
open Subgroup Equiv
namespace Theory.SpecificGroups.SymmetricFive

private theorem involution_even_of_not_swap (a : Perm (Fin 5))
    (ha2 : a^2=1) (ha : ¬a.IsSwap) : Perm.sign a=1 := by
  by_cases ha1 : a=1
  · rw [ha1,map_one]
  have horder : orderOf a=2 := orderOf_eq_prime ha2 ha1
  obtain ⟨n,hn⟩ := Perm.cycleType_prime_order (σ:=a) (by rw [horder]; decide)
  have hb := a.sum_cycleType_le
  rw [hn,horder,Multiset.sum_replicate] at hb
  have hnl : n≤1 := by
    simp only [nsmul_eq_mul,Nat.cast_id,Fintype.card_fin] at hb
    omega
  interval_cases n
  · exact (ha (Perm.isSwap_iff_cycleType.mpr (by simpa [horder] using hn))).elim
  · rw [Perm.sign_of_cycleType,hn,horder]
    norm_num

/-- An involutory automorphism with the specified cubic action and an
inverted square root is conjugation by an actual transposition of S5. -/
theorem involutive_automorphism_transposition_of_inverted_root
    (α : MulAut (Perm (Fin 5))) (hα2 : α^2=1)
    (s d : Perm (Fin 5)) (hs : orderOf s=3) (hd : orderOf d=4)
    (hdinv : α d=d⁻¹) (hsc : α s=d^2*s*(d^2)⁻¹) :
    ∃ a : Perm (Fin 5), a.IsSwap ∧ α=MulAut.conj a := by
  obtain ⟨a,ha⟩ := Perm.conj_surjective_of_degree (by decide : 5≤5) (by decide) α
  have ha2 : a^2=1 := conj_injective (by rw [map_pow,ha,hα2,map_one])
  have hd4 : d^4=1 := hd ▸ pow_orderOf_eq_one d
  have hv2 : (d^2)^2=1 := by rw [←pow_mul]; exact hd4
  have hαv : α (d^2)=d^2 := by
    rw [map_pow,hdinv,inv_pow]
    exact inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hv2)
  have hav : Commute a (d^2) := by
    have hh : a*d^2*a⁻¹=d^2 := by simpa only [←ha,MulAut.conj_apply] using hαv
    exact mul_inv_eq_iff_eq_mul.mp hh
  by_contra hnot
  have hna : ¬a.IsSwap := fun hswa => hnot ⟨a,hswa,ha.symm⟩
  have haeven := involution_even_of_not_swap a ha2 hna
  let b := (d^2)⁻¹*a
  have hb2 : b^2=1 := by
    rw [(hav.symm.inv_left).mul_pow,inv_pow,hv2,ha2,inv_one,mul_one]
  have hbs : Commute b s := by
    have hh : a*s*a⁻¹=d^2*s*(d^2)⁻¹ := by
      simpa only [←ha,MulAut.conj_apply] using hsc
    apply mul_inv_eq_iff_eq_mul.mp
    change ((d^2)⁻¹*a)*s*((d^2)⁻¹*a)⁻¹=s
    calc
      _ = (d^2)⁻¹*(a*s*a⁻¹)*d^2 := by group
      _ = s := by rw [hh]; group
  have hbeven : Perm.sign b=1 := by
    change Perm.sign ((d^2)⁻¹*a)=1
    rw [map_mul,map_inv,map_pow,haeven,mul_one]
    have hh : (Perm.sign d)^2=1 := by
      rcases Int.units_eq_one_or (Perm.sign d) with hh | hh <;> rw [hh] <;> norm_num
    rw [hh,inv_one]
  have hb1 : b=1 := by
    by_contra hb1
    have hbo : orderOf b=2 := orderOf_eq_prime hb2 hb1
    have hdvd : 3∣Nat.card (centralizer ({b}:Set (Perm (Fin 5)))) := by
      have hh := orderOf_dvd_natCard (⟨s,mem_centralizer_singleton_iff.mpr hbs.eq.symm⟩ :
        centralizer ({b}:Set (Perm (Fin 5))))
      simpa only [orderOf_mk,hs] using hh
    have hswap := involution_isSwap_of_three_dvd_centralizer b hbo hdvd
    have hh := hswap.sign_eq
    rw [hbeven] at hh
    norm_num at hh
  have hae : a=d^2 := by
    exact (inv_mul_eq_one.mp hb1).symm
  have had : α d=d := by
    rw [←ha,hae,MulAut.conj_apply]
    group
  have hdi : d⁻¹=d := hdinv.symm.trans had
  have hd2 : d^2=1 := by
    calc
      d^2=d⁻¹*d := by rw [pow_two]; exact congrArg (· * d) hdi.symm
      _=1 := inv_mul_cancel d
  have hdvd := orderOf_dvd_of_pow_eq_one hd2
  rw [hd] at hdvd
  norm_num at hdvd

end Theory.SpecificGroups.SymmetricFive
