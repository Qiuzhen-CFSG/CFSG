module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.OmegaAction.Setup
public import Theory.GroupTheory.WreathTwoSylowModel
public import Theory.GroupAction.Extraspecial27ElementaryActor
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The omega subgroup of the extraspecial center-action kernel

Let P be a Sylow two-subgroup of the concrete orthogonal actor, acting
faithfully on an extraspecial group F of order 27. The first omega subgroup
of its center-fixing image is the center of P, embedded in that same actor.

The actual Sylow equivalence identifies P with the dihedral group of order
eight. Since Z(F) has order three, its automorphism group has order two,
so every square fixes Z(F). In particular the central dihedral involution
lies in the action kernel on Z(F). A noncentral kernel involution would
join it in a center-fixing Klein four subgroup, contradicting the faithful
elementary actor bound. Thus the kernel's involutions are exactly Z(P).
The last step uses the defining generation property of the ambient omega
subgroup and retains the original subgroup embedding.

This is a conditional action calculation for the equality after 15.3.49(b),
Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1143.
Constructing the faithful action on the source quotient and identifying
its center-fixing image with the barred quotient centralizer are separate
obligations of the source assembly.
-/

open Subgroup

private theorem dihedral_center : ∀ x : DihedralGroup 4, x ∈ center (DihedralGroup 4) ↔ x = 1 ∨ x = .r 2 := by
  decide +kernel

private instance (x : DihedralGroup 4) :
    DecidablePred (· ∈ centralizer ({x} : Set (DihedralGroup 4))) :=
  fun y => decidable_of_iff (y * x = x * y) mem_centralizer_singleton_iff.symm

private theorem dihedral_centralizer_elements : ∀ x : DihedralGroup 4, x ^ 2 = 1 → x ∉ center (DihedralGroup 4) →
    (∀ y ∈ centralizer ({x} : Set (DihedralGroup 4)),
      y = 1 ∨ y = .r 2 ∨ y = x ∨ y = x * .r 2) := by
  decide +kernel

private theorem dihedral_centralizer_card_pow : ∀ x : DihedralGroup 4, x ^ 2 = 1 → x ∉ center (DihedralGroup 4) →
    Nat.card (centralizer ({x} : Set (DihedralGroup 4))) = 4 ∧
      (∀ y ∈ centralizer ({x} : Set (DihedralGroup 4)), y ^ 2 = 1) := by
  simp_rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem center_square_fixed {F : Type*} [Group F] [Finite F]
    [IsExtraspecial 3 F] (a : MulAut F) (z : F) (hz : z ∈ center F) :
    (a ^ 2) z = z := by
  let _ : IsCyclic (center F) := isCyclic_of_prime_card (IsExtraspecial.center_order_p 3 F)
  have hcard : Nat.card (MulAut (center F)) = 2 := by
    rw [IsCyclic.card_mulAut, IsExtraspecial.center_order_p 3 F]
    decide
  have hpow : (MulAut.characteristic (center F) a) ^ 2 = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  exact congrArg (fun b : MulAut (center F) => (b ⟨z, hz⟩ : F)) hpow

private theorem dihedral_kernel_involutions {F : Type*} [Group F] [Finite F]
    [IsExtraspecial 3 F] (hF : Nat.card F = 27)
    (action : DihedralGroup 4 →* MulAut F) (hinj : Function.Injective action)
    (x : DihedralGroup 4) :
    (x ∈ (fixingSubgroup (MulAut F) (center F : Set F)).comap action ∧ x ^ 2 = 1) ↔
      x ∈ center (DihedralGroup 4) := by
  let K := (fixingSubgroup (MulAut F) (center F : Set F)).comap action
  have hz : DihedralGroup.r 2 ∈ K := by
    rw [show (DihedralGroup.r 2 : DihedralGroup 4) = DihedralGroup.r 1 ^ 2 by decide]
    change action (DihedralGroup.r 1 ^ 2) ∈ fixingSubgroup (MulAut F) (center F : Set F)
    rw [map_pow, mem_fixingSubgroup_iff]
    exact center_square_fixed (action (.r 1))
  constructor
  · rintro ⟨hx, hpow⟩
    by_contra hnoncentral
    let B := centralizer ({x} : Set (DihedralGroup 4))
    obtain ⟨hcard, hexp⟩ := dihedral_centralizer_card_pow x hpow hnoncentral
    have hBK : B ≤ K := by
      intro y hy
      rcases dihedral_centralizer_elements x hpow hnoncentral y hy with h | h | h | h
      · exact h ▸ K.one_mem
      · exact h ▸ hz
      · exact h ▸ hx
      · exact h ▸ K.mul_mem hx hz
    let _ : IsElementaryAbelian 2 B := {
      toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hcard
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        (fun y => Subtype.ext (hexp y y.property)) }
    have hsmall := MulAut.elementary_two_center_preserving_card_le_two hF
      (action.comp B.subtype) (hinj.comp B.subtype_injective)
      (fun y => (mem_fixingSubgroup_iff (MulAut F)).mp (hBK y.property))
    change Nat.card B = 4 at hcard
    omega
  · intro hx
    rcases (dihedral_center x).mp hx with rfl | rfl
    · exact ⟨K.one_mem, one_pow 2⟩
    · exact ⟨hz, by decide⟩

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal

/-- For the supplied faithful extraspecial action, the involutions of the
center-fixing image generate precisely the actual Sylow center, embedded
in the orthogonal actor. The action and its faithfulness remain explicit. -/
public theorem orthogonal_sylow_centerFixingImage_omega
    (P : Sylow 2 OrthogonalActor) {F : Type*} [Group F] [Finite F]
    [IsExtraspecial 3 F] (hF : Nat.card F = 27)
    (ρ : P →* MulAut F) (hinj : Function.Injective ρ) :
    omegaOneAmbient (centerFixingImage (P : Subgroup OrthogonalActor) ρ) =
      (center P).map (P : Subgroup OrthogonalActor).subtype := by
  obtain ⟨e⟩ := wreath_two_sylow_mulEquiv_dihedral_four P
  let action : DihedralGroup 4 →* MulAut F := ρ.comp e.symm.toMonoidHom
  have hfaith : Function.Injective action := hinj.comp e.symm.injective
  apply le_antisymm
  · apply (omegaOneAmbient_le_iff _ _).mpr
    rintro x ⟨p, hp, rfl⟩ hpow
    have hp2 : p ^ 2 = 1 := Subtype.ext hpow
    have hd : e p ∈ center (DihedralGroup 4) := by
      apply (dihedral_kernel_involutions hF action hfaith (e p)).mp
      constructor
      · simpa [action] using hp
      · rw [← map_pow, hp2, map_one]
    refine ⟨p, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro q
    apply e.injective
    simpa only [map_mul] using mem_center_iff.mp hd (e q)
  · rintro x ⟨p, hp, rfl⟩
    have hd : e p ∈ center (DihedralGroup 4) := (centerCongr e ⟨p, hp⟩).property
    obtain ⟨hk, hp2⟩ := (dihedral_kernel_involutions hF action hfaith (e p)).mpr hd
    have hpk : p ∈ (fixingSubgroup (MulAut F) (center F : Set F)).comap ρ := by
      simpa [action] using hk
    have hp2' : p ^ 2 = 1 := e.injective (by simpa only [map_pow, map_one] using hp2)
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl (p : OrthogonalActor)
      ⟨p, hpk, rfl⟩ (congrArg Subtype.val hp2')

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal
