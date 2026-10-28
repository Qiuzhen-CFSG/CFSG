module

public import Theory.GroupTheory.PerfectCentralCover
public import Theory.GroupTheory.Commutator.CentralExtensionPairing

/-!
# Central kernels and a section over a subgroup of prime-to-p index

If a perfect central cover splits over a subgroup P, the derived subgroup of
the preimage of P lies in the section image. Transfer to the abelianization
of that preimage forces every central element of prime order p into its
commutator subgroup when p does not divide the index. The section image
meets the central kernel trivially, so p cannot divide the kernel order.

This is the transfer step in the defining-prime multiplier calculation for
Sp₄ in Aschbacher–Smith, I.1.3, printed p.407, citing GLS98 §6.1. The
symplectic application uses the literal unipotent subgroup and its odd index;
no presentation or lifted-root relation is presumed here.
-/

public section

open scoped commutatorElement
open Subgroup

namespace PerfectCentralCovering

/-- A perfect central cover has kernel of order prime to `p` if it splits
on a subgroup whose index is prime to `p`. The section is required to commute
with the literal subgroup inclusion. -/
theorem not_dvd_card_kernel_of_section
    {E G : Type*} [Group E] [Finite E] [Group G]
    (f : Cover E G) {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) (hp : ¬ p ∣ P.index)
    (s : P →* E) (hs : f.toMonoidHom.comp s = P.subtype) :
    ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  let : Group.IsPerfect E := f.isPerfect
  let H := P.comap f.toMonoidHom
  have hderived : ⁅H, H⁆ ≤ s.range := by
    apply Subgroup.commutator_le.mpr
    intro a ha b hb
    have hsa : f.toMonoidHom (s ⟨f.toMonoidHom a, ha⟩) = f.toMonoidHom a :=
      DFunLike.congr_fun hs _
    have hsb : f.toMonoidHom (s ⟨f.toMonoidHom b, hb⟩) = f.toMonoidHom b :=
      DFunLike.congr_fun hs _
    rw [CentralExtension.commutator_eq_of_image_eq f.toMonoidHom f.ker_le_center
      hsa.symm hsb.symm]
    exact ⟨⁅(⟨f.toMonoidHom a, ha⟩ : P), (⟨f.toMonoidHom b, hb⟩ : P)⁆,
      map_commutatorElement s _ _⟩
  intro hd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hd
  let x : H := ⟨z, by
    change f.toMonoidHom z ∈ P
    rw [z.property]
    exact P.one_mem⟩
  have hxcentral : (x : E) ∈ center E := f.ker_le_center z.property
  let q : H →* Abelianization H := Abelianization.of
  have ht : MonoidHom.transfer q x = 1 :=
    Abelianization.commutator_subset_ker _ Group.IsPerfect.mem_commutator
  have hkey : ∀ (k : ℕ) (g : E), g⁻¹ * (x : E)^k * g ∈ H →
      g⁻¹ * (x : E)^k * g = (x : E)^k := by
    intro k g _
    have hc := mem_center_iff.mp ((center E).pow_mem hxcentral k) g
    rw [mul_assoc, hc.symm, inv_mul_cancel_left]
  have hpow : q x ^ H.index = 1 := by
    have he : MonoidHom.transfer q x = q (x ^ H.index) :=
      MonoidHom.transfer_eq_pow q (x : E) hkey
    rw [he, map_pow] at ht
    exact ht
  have hxpow : x ^ p = 1 := by
    apply Subtype.ext
    exact congrArg (fun y : f.toMonoidHom.ker => (y : E))
      (hz ▸ pow_orderOf_eq_one z)
  have hqp : orderOf (q x) ∣ p := orderOf_dvd_of_pow_eq_one (by
    rw [← map_pow, hxpow, map_one])
  have hindex : H.index = P.index := P.index_comap_of_surjective f.surjective
  have hcop : (orderOf (q x)).Coprime H.index := by
    rw [hindex]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp |>.coprime_dvd_left hqp
  have hqx : q x = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl (orderOf_dvd_of_pow_eq_one hpow))
  have hxderived : x ∈ commutator H := by
    change x ∈ Abelianization.of.ker at hqx
    rwa [Abelianization.ker_of] at hqx
  have hzderived : (z : E) ∈ ⁅H, H⁆ := by
    rw [← map_subtype_commutator]
    exact ⟨x, hxderived, rfl⟩
  obtain ⟨y, hy⟩ := hderived hzderived
  have hy1 : y = 1 := by
    apply Subtype.ext
    change (y : G) = 1
    exact (DFunLike.congr_fun hs y).symm.trans
      ((congrArg f.toMonoidHom hy).trans z.property)
  have hz1 : z = 1 := Subtype.ext (by simpa [hy1] using hy.symm)
  rw [hz1, orderOf_one] at hz
  exact (Fact.out : p.Prime).ne_one hz.symm

end PerfectCentralCovering

end
