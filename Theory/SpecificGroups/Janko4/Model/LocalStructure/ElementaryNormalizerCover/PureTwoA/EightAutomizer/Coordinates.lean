module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Core
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.Defect

/-!
# The eight-bit coordinates on the actual native eight

The existing native coordinate bijection is multiplicative for XOR. This
identifies the finite automizer calculation with the actual subgroup, including
the exact sixteen already proved invariant under its whole normalizer.
Source: Kleidman--Wilson (1988), Corollary 2.3.6.
-/

set_option backward.isDefEq.respectTransparency true
public noncomputable section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer
open ElementaryEightGeometry ElementaryEightGeometry.Loewy GeneratorCertificates
open scoped IsMulCommutative
attribute [local irreducible] modelGroup matrixA matrixB nativeMask correctedLift

private theorem coordinates_add (v w : (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2)) :
    eightCoordinates 0 (v+w) = eightCoordinates 0 v + eightCoordinates 0 w := by
  simp only [eightCoordinates, kernelSum, liftSum, Prod.fst_add, Prod.snd_add,
    Pi.add_apply, add_smul, Finset.sum_add_distrib]
  abel

theorem maskElement_xor (m n : Mask) :
    maskElement (xor m n) = maskElement m * maskElement n := by
  have hc : maskCoordinates (xor m n) = maskCoordinates m + maskCoordinates n := by
    apply Prod.ext <;> funext i <;> exact bit_xor m.val n.val _
  unfold maskElement
  rw [hc, coordinates_add]
  rfl

theorem maskElement_zero : maskElement 0 = 1 := by
  simp [maskElement, maskCoordinates, eightCoordinates, kernelSum, liftSum, bit]

private theorem maskCoordinates_surjective : Function.Surjective maskCoordinates := by
  rintro ⟨a,b⟩
  obtain ⟨m,ha,hb⟩ := exists_mask_coordinates a b
  exact ⟨m, Prod.ext ha hb⟩

private theorem maskCoordinates_injective : Function.Injective maskCoordinates :=
  (maskCoordinates_surjective.bijective_of_nat_card_le (by
    simp only [Nat.card_fin, Nat.card_prod, Nat.card_fun, Nat.card_zmod]
    decide)).1

theorem maskElement_injective : Function.Injective maskElement := by
  intro m n h
  apply maskCoordinates_injective
  apply eightCoordinates_injective 0
  exact congrArg Additive.ofMul (Subtype.ext h)

theorem maskElement_basis (i : Fin 8) : maskElement (bitBasis i) = nativeGenerator i := by
  fin_cases i <;>
    simp [bitBasis, maskElement, maskCoordinates, eightCoordinates, kernelSum,
      liftSum, Fin.sum_univ_succ, bit, nativeGenerator, Nat.testBit, Fin.addCases]

/-- Actual elements of the native eight, retaining their literal binary masks. -/
def nativeParam : Mask ≃ nativeEight 0 :=
  Equiv.ofBijective (fun m => ⟨maskElement m, maskElement_mem m⟩)
    ⟨fun _ _ h => maskElement_injective (congrArg Subtype.val h), by
      intro x
      have hx : (x : Model) ∈ Set.range maskElement := by
        rw [maskElement_range]
        exact x.property
      obtain ⟨m,hm⟩ := hx
      exact ⟨m,Subtype.ext hm⟩⟩

theorem nativeParam_coe (m : Mask) : (nativeParam m : Model) = maskElement m := by
  change (nativeParam.toFun m).val = _
  unfold nativeParam
  rfl

set_option maxRecDepth 10000 in
theorem inK_iff_isotropic (m : Mask) :
    inK m = true ↔ maskElement m ∈ isotropicSubgroup := by
  rw [maskElement_mem_isotropic_iff]
  have h : ∀ m : Mask, inK m = true ↔ isotropicCode m := by decide +kernel
  exact h m

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer
