module

public import Theory.GroupTheory.WreathTwoSylowCentralizer
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Pulling back the wreath Sylow centralizer bound

Commuting images in the faithful wreath quotient lie in the Sylow
centralizer of the image of V. Its concrete centralizer theorem gives
image containment and order at most four. Pulling back containment within
the supplied Sylow uses its intersection with the kernel, not the whole
ambient kernel. The cardinal identity for a homomorphism then gives the
unquotiented cardinal inequality used in Stellmacher (9.1), relation (9),
journal p.47 of `refs/files/stellmacher-n-group.pdf`. The supplied Sylow
and the actual surjection remain part of the statement.
-/

open scoped commutatorElement


/-- Pull back the small Sylow centralizer of the image through the actual wreath quotient. -/
public theorem wreath_quotient_sylow_control
    {G : Type*} [Group G] [Finite G]
    (projection : G →* RegularWreathProduct
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2)))
    (hsurj : Function.Surjective projection)
    (sylow : Sylow 2 G) (U V : Subgroup G)
    (hUS : U ≤ (sylow : Subgroup G)) (hVS : V ≤ (sylow : Subgroup G))
    (hfour : 4 ≤ projection.ker.relIndex V)
    (hcomm : ⁅U, V⁆ ≤ projection.ker) :
    U ≤ V ⊔ ((sylow : Subgroup G) ⊓ projection.ker) ∧
      Nat.card U ≤ 4 * Nat.card (U ⊓ projection.ker : Subgroup G) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let imageSylow := sylow.mapSurjective hsurj
  have hVimage : 4 ≤ Nat.card (V.map projection) := by
    rwa [← Subgroup.relIndex_ker]
  have hVimageS : V.map projection ≤ (imageSylow : Subgroup _) :=
    Subgroup.map_mono hVS
  have hUimageS : U.map projection ≤ (imageSylow : Subgroup _) :=
    Subgroup.map_mono hUS
  have hUcentral : U.map projection ≤ Subgroup.centralizer (V.map projection : Set _) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    rw [← Subgroup.map_commutator]
    exact le_bot_iff.mp ((Subgroup.map_mono hcomm).trans (by simp))
  obtain ⟨hcontain, hbound⟩ := wreath_two_sylow_centralizer_le_of_card_ge_four
    imageSylow (V.map projection) hVimageS hVimage
  have himage := le_inf hUimageS hUcentral
  constructor
  · intro element helement
    obtain ⟨preimage, hpreimage, heq⟩ := hcontain (himage
      (Subgroup.mem_map_of_mem projection helement))
    have hkernel : preimage⁻¹ * element ∈ projection.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, heq, inv_mul_cancel]
    have hsylow : preimage⁻¹ * element ∈ (sylow : Subgroup G) :=
      (sylow : Subgroup G).mul_mem ((sylow : Subgroup G).inv_mem (hVS hpreimage))
        (hUS helement)
    have hmem := (V ⊔ ((sylow : Subgroup G) ⊓ projection.ker)).mul_mem
      (Subgroup.mem_sup_left hpreimage) (Subgroup.mem_sup_right ⟨hsylow, hkernel⟩)
    simpa only [mul_inv_cancel_left] using hmem
  · have hcard : Nat.card (U.map projection) ≤ 4 :=
      (Subgroup.card_le_of_le himage).trans hbound
    have hmul : Nat.card (U ⊓ projection.ker : Subgroup G) *
        Nat.card (U.map projection) = Nat.card U := by
      rw [← Subgroup.relIndex_ker, ← Subgroup.inf_relIndex_left]
      simpa only [Subgroup.relIndex_bot_left] using
        Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (U ⊓ projection.ker) U bot_le inf_le_left
    rw [← hmul, mul_comm 4]
    exact Nat.mul_le_mul_left _ hcard


