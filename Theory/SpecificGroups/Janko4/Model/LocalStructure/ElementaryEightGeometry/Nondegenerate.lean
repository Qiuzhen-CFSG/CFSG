module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Pairing

/-!
# Nondegeneracy on the native elementary eights

The four fixed-kernel vectors pair to zero with one another. Their invertible
cross-pairing with the four lifts makes the eight displayed vectors independent.
The checked order 256 then gives coordinates for every element. Pairing a
radical vector first with the kernel vectors and then with the lifts forces
both coordinate blocks to vanish. No chosen or abstract form replaces the
intrinsic full-centralizer form.
Source: Kleidman--Wilson (1988), Propositions 2.3.4--2.3.5 and Corollary 2.3.6.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Subgroup Cardinality KernelCount QuotientCount.Image SylowCore SylowCore.Transport
open LargeCenterRadicals.OuterHalf
open scoped IsMulCommutative
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup localX localY basis
local notation "L" => SylowCore.Local

private theorem kernelPair_inner (r : Fin 2) (j k : Fin 4) :
    InnerRelated ((nativeMask (kernelPairMasks r j) : L) : Model)
      ((nativeMask (kernelPairMasks r k) : L) : Model) := by
  apply (kernelPair_inner_iff r j _ (nativeMask_commute _ _)).mpr
  rw [nativeMask_projection]
  exact ⟨rfl,rfl⟩

theorem nativeEight_kernel_pairing (r : Fin 2) (j k : Fin 4) :
    intrinsicElementaryForm (nativeEight r) (kernelVector r j) (kernelVector r k) = 0 := by
  change outerValue ((nativeMask (kernelPairMasks r j) : L) : Model)
    ((nativeMask (kernelPairMasks r k) : L) : Model) = 0
  simp only [outerValue, kernelPair_inner, or_true, ite_true]

def kernelSum (r : Fin 2) (v : Fin 4 → ZMod 2) : Additive (nativeEight r) :=
  ∑ j, v j • kernelVector r j

def liftSum (r : Fin 2) (v : Fin 4 → ZMod 2) : Additive (nativeEight r) :=
  ∑ j, v j • liftVector r j

private def rowPairing (r : Fin 2) (v : Fin 4 → ZMod 2) (k : Fin 4) : ZMod 2 :=
  ∑ j, v j * pairingEntry r j k
private def colPairing (r : Fin 2) (v : Fin 4 → ZMod 2) (k : Fin 4) : ZMod 2 :=
  ∑ j, v j * pairingEntry r k j

private theorem rowPairing_injective : ∀ r, Function.Injective (rowPairing r) := by decide +kernel
private theorem colPairing_injective : ∀ r, Function.Injective (colPairing r) := by decide +kernel

private theorem kernelSum_pairing (r : Fin 2) (v : Fin 4 → ZMod 2) (k : Fin 4) :
    intrinsicElementaryForm (nativeEight r) (kernelSum r v) (liftVector r k) = rowPairing r v k := by
  simp only [kernelSum, rowPairing, map_sum, LinearMap.sum_apply, LinearMap.BilinForm.smul_left,
    nativeEight_pairing]

private theorem liftSum_pairing (r : Fin 2) (v : Fin 4 → ZMod 2) (k : Fin 4) :
    intrinsicElementaryForm (nativeEight r) (kernelVector r k) (liftSum r v) = colPairing r v k := by
  simp only [liftSum, colPairing, map_sum, LinearMap.BilinForm.smul_right, nativeEight_pairing]

private theorem kernelSum_zero_pairing (r : Fin 2) (v : Fin 4 → ZMod 2) (k : Fin 4) :
    intrinsicElementaryForm (nativeEight r) (kernelVector r k) (kernelSum r v) = 0 := by
  simp only [kernelSum, map_sum, LinearMap.BilinForm.smul_right, nativeEight_kernel_pairing, mul_zero, Finset.sum_const_zero]

/-- Coordinates supplied by the four kernel elements and four literal lifts. -/
def eightCoordinates (r : Fin 2) (v : (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2)) :
    Additive (nativeEight r) := kernelSum r v.1 + liftSum r v.2

theorem eightCoordinates_injective (r : Fin 2) : Function.Injective (eightCoordinates r) := by
  intro v w h
  have h2 : v.2 = w.2 := by
    apply colPairing_injective r
    funext k
    have hk := congrArg (intrinsicElementaryForm (nativeEight r) (kernelVector r k)) h
    simpa only [eightCoordinates, map_add, kernelSum_zero_pairing, liftSum_pairing,
      zero_add] using hk
  have h1 : v.1 = w.1 := by
    apply rowPairing_injective r
    funext k
    have hk : kernelSum r v.1 = kernelSum r w.1 := by
      apply add_right_cancel (b := liftSum r w.2)
      simpa only [eightCoordinates,h2] using h
    simpa only [kernelSum_pairing] using
      congrArg (fun x => intrinsicElementaryForm (nativeEight r) x (liftVector r k)) hk
  exact Prod.ext h1 h2

theorem eightCoordinates_surjective (r : Fin 2) : Function.Surjective (eightCoordinates r) := by
  refine ((eightCoordinates_injective r).bijective_of_nat_card_le ?_).2
  change Nat.card (nativeEight r) ≤ _
  rw [nativeEight_card, Nat.card_prod, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  decide

private theorem separating (r : Fin 2) : (intrinsicElementaryForm (nativeEight r)).SeparatingLeft := by
  intro x hx
  obtain ⟨⟨v,w⟩,rfl⟩ := eightCoordinates_surjective r x
  have hw : w = 0 := by
    apply colPairing_injective r
    funext k
    have hk := hx (kernelVector r k)
    rw [(intrinsicElementaryForm_isSymm (nativeEight r)).eq] at hk
    simpa only [eightCoordinates, LinearMap.BilinForm.add_right, kernelSum_zero_pairing,
      liftSum_pairing, zero_add, colPairing, Pi.zero_apply, zero_mul, Finset.sum_const_zero] using hk
  have hv : v = 0 := by
    apply rowPairing_injective r
    funext k
    have hk := hx (liftVector r k)
    simpa only [eightCoordinates, hw, liftSum, Pi.zero_apply, zero_smul, Finset.sum_const_zero,
      add_zero, kernelSum_pairing, rowPairing, zero_mul] using hk
  simp [eightCoordinates, hv, hw, kernelSum, liftSum]

/-- Nondegeneracy of the actual intrinsic form on both native order-256 subgroups. -/
theorem nativeEight_nondegenerate (r : Fin 2) :
    (intrinsicElementaryForm (nativeEight r)).Nondegenerate := by
  refine ⟨separating r, ?_⟩
  intro y hy
  apply separating r y
  intro x
  rw [(intrinsicElementaryForm_isSymm (nativeEight r)).eq]
  exact hy x

end Janko4.LocalStructure.ElementaryEightGeometry
