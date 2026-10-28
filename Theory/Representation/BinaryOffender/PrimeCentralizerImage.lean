module
public import Theory.Representation.BinaryOffender.PrimeCentralizerFixed
/-!
# Faithful elementary action on the odd fixed-space image

Let R be a normal odd prime subgroup and B an elementary two-subgroup in
a faithful binary representation. On C_V(C_B(R)), the image of B acts
faithfully on the image of R. Lift a commuting image element to B and use
the established faithfulness on R to recover actual commutation; the exact
fixed-space kernel then kills its image.

Source: the A.1.18 reduction used in Aschbacher–Smith 14.5.11,
printed pp.1015–1016, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- The restricted elementary image has trivial centralizer on the odd image. -/
theorem prime_fixed_image_centralizer
    (hf : Function.Injective ρ) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (R B : Subgroup G) [R.Normal] [IsElementaryAbelian 2 B] (hR : IsPGroup p R) :
    let U := fixedSpace ρ (B ⊓ centralizer (R : Set G))
    restrictedSubgroup ρ U B ⊓ centralizer
      (restrictedSubgroup ρ U R : Set (subspaceActionImage ρ U)) = ⊥ := by
  let K := B ⊓ centralizer (R : Set G)
  let U := fixedSpace ρ K
  let S := subspaceStabilizer ρ U
  let f := subspaceActionHom ρ U
  have hRs : R ≤ S := le_stabilizer_fixedSpace_of_commutator_eq_bot ρ R K
    (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mpr inf_le_right))
  obtain ⟨hkR,hkB⟩ := prime_centralizer_fixed_kernel ρ hf hp R B hR
  have hiR := (subgroupActionHom_injective_iff ρ U R hRs).mpr hkR
  apply bot_unique
  rintro i ⟨⟨b,hb,rfl⟩,hi⟩
  have hbC : (b : G) ∈ centralizer (R : Set G) := by
    intro r hr
    have hbr : (b : G) * r * (b : G)⁻¹ ∈ R :=
      (inferInstance : R.Normal).conj_mem r hr b
    have he : (⟨(b : G) * r * (b : G)⁻¹,hbr⟩ : R) = ⟨r,hr⟩ := by
      apply hiR
      change f (b * ⟨r,hRs hr⟩ * b⁻¹) = f ⟨r,hRs hr⟩
      rw [map_mul,map_mul,map_inv]
      rw [← hi (f ⟨r,hRs hr⟩) (mem_map_of_mem f hr),mul_inv_cancel_right]
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)).symm
  have hbK : (b : G) ∈ subspaceKernel ρ U B := by
    rw [hkB]
    exact ⟨hb,hbC⟩
  change f b = 1
  apply subspaceImageRepresentation_injective ρ U
  ext w
  exact hbK.2 w w.property
end Representation.BinaryOffender
