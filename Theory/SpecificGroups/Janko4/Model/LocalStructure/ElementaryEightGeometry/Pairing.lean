module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.NativeSubgroups
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.PairCharacter
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.OuterHalf.Symmetry
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Intrinsic kernel--lift pairings

The actual full-centralizer residual characters give the cross-pairing matrix
between four displayed kernel pairs and four corrected lifts in each native
elementary subgroup. Each matrix has determinant one over the binary field.
This calculation uses `intrinsicElementaryForm`, whose outer-half definition
and ambient conjugation conventions are retained throughout.
Source: Kleidman--Wilson (1988), Propositions 2.3.4--2.3.5 and Corollary 2.3.6.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Subgroup Cardinality KernelCount QuotientCount.Image SylowCore SylowCore.Transport
open LargeCenterRadicals.OuterHalf
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup localX localY basis
local notation "L" => SylowCore.Local
local notation "E" => localKernel matrixA_mul_self matrixB_pow_four
local notation "π" => starProjection matrixA_mul_self matrixB_pow_four
local notation "e" => maskEquiv matrixA_mul_self matrixB_pow_four

private theorem mask_bound : ∀ r j, kernelPairMasks r j < 2048 := by decide +kernel

private theorem masks_fixed : ∀ (r : Fin 2) (j : Fin 4),
    fixedTest (unprimedRow (r.castLE (by decide)))
      ⟨kernelPairMasks r j,mask_bound r j⟩ := by decide +kernel

theorem kernelPair_mem_centralKernel (r : Fin 2) (j : Fin 4) :
    nativeMask (kernelPairMasks r j) ∈ centralKernel r := by
  apply mem_map.mpr
  refine ⟨e ⟨kernelPairMasks r j,mask_bound r j⟩,?_,rfl⟩
  exact (mask_mem_pairRow_centralizer_iff (liftClosure r) _
    (liftClosure_projection r) _).mpr (masks_fixed r j)

theorem kernelPair_mem_localEight (r : Fin 2) (j : Fin 4) :
    nativeMask (kernelPairMasks r j) ∈ localEight r :=
  (show centralKernel r ≤ localEight r from le_sup_right) (kernelPair_mem_centralKernel r j)

theorem correctedGenerator_mem_localEight (r : Fin 2) (j : Fin 4) :
    correctedGenerator r j ∈ localEight r :=
  (show liftClosure r ≤ localEight r from le_sup_left) (correctedGenerator_mem r j)

def pairingEntry : Fin 2 → Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  ![![![0,0,0,1], ![1,0,0,1], ![1,0,1,1], ![0,1,0,1]],
    ![![0,0,0,1], ![1,0,0,0], ![0,0,1,1], ![0,1,0,1]]]

private theorem pair_fix_iff : ∀ (r : Fin 2) (j k : Fin 4),
    ((pairRowGenerator (r.castLE (by decide)) k).val (kernelPairs r j).1 = (kernelPairs r j).1 ∧
      (pairRowGenerator (r.castLE (by decide)) k).val (kernelPairs r j).2 = (kernelPairs r j).2) ↔
      pairingEntry r j k = 0 := by
  intro r j k
  fin_cases r <;> fin_cases j <;> fin_cases k <;> decide +kernel

theorem kernelPair_correctedGenerator_inner (r : Fin 2) (j k : Fin 4) :
    InnerRelated ((nativeMask (kernelPairMasks r j) : L) : Model)
      ((correctedGenerator r k : L) : Model) ↔ pairingEntry r j k = 0 := by
  have hc : Commute (nativeMask (kernelPairMasks r j)) (correctedGenerator r k) :=
    setLike_mul_comm (kernelPair_mem_localEight r j)
      (correctedGenerator_mem_localEight r k)
  rw [kernelPair_inner_iff r j _ hc, correctedGenerator_projection]
  exact pair_fix_iff r j k

private theorem kernelPair_ne_one (r : Fin 2) (j : Fin 4) :
    ((nativeMask (kernelPairMasks r j) : L) : Model) ≠ 1 := by
  intro h
  have hs : nativeMask 1 = 1 := by
    have hlocal : nativeMask (kernelPairMasks r j) = 1 := Subtype.ext h
    rw [← pairMover_seed] at hlocal
    exact (MulAut.conj (pairMover r j)).injective
      (hlocal.trans (map_one (MulAut.conj (pairMover r j))).symm)
  have hseed : nativeMask 1 = InvolutionCentralizers.Second.seed :=
    Simplicity.Max1Fusion.KernelOrbits.maskValue_one matrixA_mul_self matrixB_pow_four
  have ho := InvolutionCentralizers.Second.seed_order
  have hamb : (InvolutionCentralizers.Second.seed : Model) = 1 :=
    congrArg Subtype.val (hseed.symm.trans hs)
  rw [hamb, orderOf_one] at ho
  omega

theorem kernelPair_correctedGenerator_outerValue (r : Fin 2) (j k : Fin 4) :
    outerValue ((nativeMask (kernelPairMasks r j) : L) : Model)
      ((correctedGenerator r k : L) : Model) = pairingEntry r j k := by
  unfold outerValue
  simp only [kernelPair_ne_one r j, false_or, kernelPair_correctedGenerator_inner]
  fin_cases r <;> fin_cases j <;> fin_cases k <;> decide +kernel

def kernelVector (r : Fin 2) (j : Fin 4) : Additive (nativeEight r) :=
  Additive.ofMul ⟨(nativeMask (kernelPairMasks r j) : Model),
    mem_map_of_mem (L).subtype (kernelPair_mem_localEight r j)⟩

def liftVector (r : Fin 2) (j : Fin 4) : Additive (nativeEight r) :=
  Additive.ofMul ⟨(correctedGenerator r j : Model),
    mem_map_of_mem (L).subtype (correctedGenerator_mem_localEight r j)⟩

/-- The intrinsic, full-centralizer form has the displayed invertible cross block. -/
theorem nativeEight_pairing (r : Fin 2) (j k : Fin 4) :
    intrinsicElementaryForm (nativeEight r) (kernelVector r j) (liftVector r k) =
      pairingEntry r j k := kernelPair_correctedGenerator_outerValue r j k

theorem pairingEntry_det (r : Fin 2) : Matrix.det (pairingEntry r) = 1 := by
  fin_cases r <;> decide +kernel

end Janko4.LocalStructure.ElementaryEightGeometry
