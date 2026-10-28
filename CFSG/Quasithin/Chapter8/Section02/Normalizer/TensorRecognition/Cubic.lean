module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.Sections
public import Theory.Representation.InvertedCubicTensor.Marked
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The marked tensor in the I/P = S₃ branch

The literal inclusion of B/U=(V∩O₂(I))/U in P/U identifies it with the
inverter-fixed space: elementary abelianness fixes B, and the two-copy
dimension identity gives equality. The explicit inverted-cubic coordinates
therefore give J⊗B/U, retaining the actual local-factor action on B/U.

The action identifications, cubic fixed-point freeness, and two-copy rank
identity are the earlier E.2.14 inputs. The full branch recognition and
their discharge remain in the tensor assembly; this module proves the
conditional cubic tensor, including its pure-tensor formula and equivariance.

Source: Aschbacher–Smith, 8.2.8(5), printed pp.718–719 (PDF pp.735–736).
-/

public section
open Subgroup InvertedCubicTensor
open scoped TensorProduct IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition
variable {G K : Type*} [Group G] [Group K] [Finite G]
  (I V U : Subgroup G)

variable [(U.subgroupOf (I.pCoreIn 2)).Normal] [(U.subgroupOf (V ⊓ I.pCoreIn 2 : Subgroup G)).Normal]
  [IsElementaryAbelian 2 ((I.pCoreIn 2) ⧸ U.subgroupOf (I.pCoreIn 2))]
  [IsElementaryAbelian 2 ((V ⊓ I.pCoreIn 2 : Subgroup G) ⧸ U.subgroupOf (V ⊓ I.pCoreIn 2 : Subgroup G))]

/-- A lift of the inverter in the original elementary V fixes the literal B/U. -/
public theorem inverter_fixes_intersection_section [IsElementaryAbelian 2 V]
    (σ : Representation F S₃ (CoreSection I U)) (v : V)
    (hn : (v : G) ∈ normalizer (I.pCoreIn 2 : Set G))
    (ha : ∀ p : I.pCoreIn 2,
      σ inverter (Additive.ofMul (QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2)) p)) =
        Additive.ofMul (QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2))
          ⟨(v : G) * (p : G) * (v : G)⁻¹,
            (mem_normalizer_iff.mp hn p).mp p.property⟩)) :
    ∀ b : IntersectionSection I V U, σ inverter ((intersectionInclusion I V U) b) = (intersectionInclusion I V U) b := by
  let _ := (inferInstance : Finite G)
  intro b
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf (V ⊓ I.pCoreIn 2 : Subgroup G)) b.toMul
  change σ inverter (quotientInclusion (I.pCoreIn 2) (V ⊓ I.pCoreIn 2) U inf_le_right
    (Additive.ofMul (QuotientGroup.mk' (U.subgroupOf (V ⊓ I.pCoreIn 2)) b))) = _
  rw [quotientInclusion_mk, ha]
  have hc : (v : G) * (b : G) = (b : G) * (v : G) :=
    congrArg Subtype.val (mul_comm v (⟨b, b.property.1⟩ : V))
  let p : I.pCoreIn 2 := ⟨b, b.property.2⟩
  have hq : QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2))
      ⟨(v : G) * (p : G) * (v : G)⁻¹, (mem_normalizer_iff.mp hn (p : G)).mp p.property⟩ =
      QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2)) p := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (v : G) * (b : G) * (v : G)⁻¹ / (b : G) ∈ U
    rw [hc, mul_inv_cancel_right]
    simp
  exact congrArg Additive.ofMul hq

/-- The cubic tensor uses the literal marked B/U, with the original action
of the commuting local factor and explicit coordinates on pure tensors. -/
theorem cubic_marked_tensor
    (σ : Representation F S₃ (CoreSection I U)) (κ : Representation F K (CoreSection I U))
    (τ : Representation F K (IntersectionSection I V U))
    (hc : ∀ k g p, κ k (σ g p) = σ g (κ k p))
    (he : ∀ k b, (intersectionInclusion I V U) (τ k b) = κ k ((intersectionInclusion I V U) b))
    (hfree : ∀ p, σ cubic p = p → p = 0)
    (hfixed : ∀ b, σ inverter ((intersectionInclusion I V U) b) = (intersectionInclusion I V U) b)
    (hd : Module.finrank F (CoreSection I U) = 2 * Module.finrank F (IntersectionSection I V U)) :
    ∃ e : BinaryPermutation.core (Fin 3) ⊗[F] (IntersectionSection I V U) ≃ₗ[F] (CoreSection I U),
      (∀ n b, e (n ⊗ₜ[F] b) = n.val 0 • (intersectionInclusion I V U) b + n.val 2 • σ cubic ((intersectionInclusion I V U) b)) ∧
      ∀ k g z,
        e (TensorProduct.map (BinaryPermutation.coreRepresentation (Fin 3) g) (τ k) z) =
          κ k (σ g (e z)) := by
  have hi := quotientInclusion_injective (I.pCoreIn 2) (V ⊓ I.pCoreIn 2 : Subgroup G) U (show (V ⊓ I.pCoreIn 2 : Subgroup G) ≤ (I.pCoreIn 2) from inf_le_right)
  have hr := marked_range_eq_fixed σ (intersectionInclusion I V U) hi hfree hfixed hd
  exact ⟨markedTensorEquiv σ (intersectionInclusion I V U) hi hr hfree,
    markedTensorEquiv_tmul σ (intersectionInclusion I V U) hi hr hfree,
    markedTensorEquiv_equivariant σ (intersectionInclusion I V U) hi hr κ τ hc he hfree⟩

/-- The source inverter lift discharges the fixed-section premise; no
identification with an abstract multiplicity space remains an input. -/
theorem cubic_marked_tensor_of_inverter [IsElementaryAbelian 2 V]
    (σ : Representation F S₃ (CoreSection I U)) (κ : Representation F K (CoreSection I U))
    (τ : Representation F K (IntersectionSection I V U))
    (hc : ∀ k g p, κ k (σ g p) = σ g (κ k p))
    (he : ∀ k b, (intersectionInclusion I V U) (τ k b) = κ k ((intersectionInclusion I V U) b))
    (hfree : ∀ p, σ cubic p = p → p = 0)
    (v : V) (hn : (v : G) ∈ normalizer (I.pCoreIn 2 : Set G))
    (ha : ∀ p : I.pCoreIn 2,
      σ inverter (Additive.ofMul (QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2)) p)) =
        Additive.ofMul (QuotientGroup.mk' (U.subgroupOf (I.pCoreIn 2))
          ⟨(v : G) * (p : G) * (v : G)⁻¹,
            (mem_normalizer_iff.mp hn p).mp p.property⟩))
    (hd : Module.finrank F (CoreSection I U) = 2 * Module.finrank F (IntersectionSection I V U)) :
    ∃ e : BinaryPermutation.core (Fin 3) ⊗[F] (IntersectionSection I V U) ≃ₗ[F] (CoreSection I U),
      (∀ n b, e (n ⊗ₜ[F] b) = n.val 0 • (intersectionInclusion I V U) b + n.val 2 • σ cubic ((intersectionInclusion I V U) b)) ∧
      ∀ k g z,
        e (TensorProduct.map (BinaryPermutation.coreRepresentation (Fin 3) g) (τ k) z) =
          κ k (σ g (e z)) :=
  cubic_marked_tensor I V U σ κ τ hc he hfree
    (inverter_fixes_intersection_section I V U σ v hn ha) hd

end CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition
