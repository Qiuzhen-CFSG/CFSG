module
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Sylow

/-!
# An eight-group with one involution mapping to a dihedral Sylow group

Every homomorphism from an eight-group with a unique involution to a finite
group with dihedral Sylow two-subgroups of order eight kills that involution.
Otherwise Cauchy's theorem makes the homomorphism injective. Its image is then
a full Sylow subgroup, but a dihedral group has distinct reflections.

This is the kernel argument in Aschbacher--Smith 14.3.21(2), printed p.998.
It avoids a separate recognition of the domain as quaternion: only its order
and uniqueness of the involution are needed by the actual quotient map.
-/

public section
open Subgroup
namespace Theory.GroupTheory

theorem involution_killed_of_dihedral_sylow
    {B D : Type*} [Group B] [Group D] [Finite B] [Finite D]
    (hB : Nat.card B = 8) (z : B)
    (hunique : ∀ x : B, orderOf x = 2 → x = z)
    (P : Sylow 2 D) (eP : P ≃* DihedralGroup 4) (f : B →* D) : f z = 1 := by
  classical
  by_contra hz
  have hp : IsPGroup 2 B := IsPGroup.of_card (n := 3) hB
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    by_contra hk
    have hkcard : 1 < Nat.card f.ker := (one_lt_card_iff_ne_bot _).mpr hk
    have hdiv : 2 ∣ Nat.card f.ker := by
      rcases (hp.to_subgroup f.ker).card_eq_or_dvd with hc | hc
      · omega
      · exact hc
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) 2 hdiv
    have hxz : (x : B) = z := hunique x ((Subgroup.orderOf_coe x).trans hx)
    exact hz (hxz ▸ x.property)
  obtain ⟨S,hS⟩ := (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  let i : B →* S := f.codRestrict (S : Subgroup D) (fun b => hS ⟨b,rfl⟩)
  have hii : Function.Injective i := fun a b he => hi (congrArg Subtype.val he)
  let eS : S ≃* DihedralGroup 4 := (S.equiv P).trans eP
  have hcS : Nat.card S = 8 := by
    rw [Nat.card_congr eS.toEquiv,DihedralGroup.nat_card]
  let j : B ≃* DihedralGroup 4 :=
    (MulEquiv.ofBijective i ((Nat.bijective_iff_injective_and_card i).mpr
      ⟨hii,hB.trans hcS.symm⟩)).trans eS
  have h0 : j.symm (DihedralGroup.sr 0) = z :=
    hunique _ ((j.symm.orderOf_eq _).trans (DihedralGroup.orderOf_sr _))
  have h1 : j.symm (DihedralGroup.sr 1) = z :=
    hunique _ ((j.symm.orderOf_eq _).trans (DihedralGroup.orderOf_sr _))
  exact (by decide : (DihedralGroup.sr 0 : DihedralGroup 4) ≠ DihedralGroup.sr 1)
    (j.symm.injective (h0.trans h1.symm))

end Theory.GroupTheory
