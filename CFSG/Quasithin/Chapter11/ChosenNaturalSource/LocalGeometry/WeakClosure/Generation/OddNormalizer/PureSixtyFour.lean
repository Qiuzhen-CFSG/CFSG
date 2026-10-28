module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity.PairOrbit
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# A pure elementary sixty-four in the native J₄ model

Purity of the original module in the first involution class does not by
itself exclude its order64. The six kernel masks 3, 5, 9, 96, 400 and 656
span a concrete elementary subgroup of that order. The finite XOR and
injectivity certificates retain the actual eleven-coordinate Mathieu
kernel. The already checked mask-three orbit and its ambient fusion show
that every nonidentity element is conjugate to the native generator a.

This diagnoses only the proposed numerical shortcut in the remaining
4.4.3 specialization. It does not realize the original full SL₃(4) action,
the elementary radical-center equality, or its full normalizer geometry.
The contradiction for that source configuration remains with
qt-d-1222-natural-odd-kernel-normalizer. Source re-exports the diagnostic
so that its actual order64/purity conclusions are not mistaken for an
impossible native subgroup.

Source context: Aschbacher--Smith 4.4.3, printed p.622. The matrix subgroup,
coordinate maps and fusion certificates retain the ATLAS J4G1-max1W1
attribution documented in the imported native modules. The six masks are
local discovery data; Lean checks all finite identities and fusion inputs.
-/

public noncomputable section
open Subgroup
open Janko4 Janko4.Cardinality Janko4.Simplicity.Max1Fusion.KernelOrbits
open Janko4.Max1RelativeRigidity
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.PureSixtyFour
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private def mask (i : Fin 64) : ℕ :=
  (if i.val.testBit 0 then 3 else 0) ^^^
  (if i.val.testBit 1 then 5 else 0) ^^^
  (if i.val.testBit 2 then 9 else 0) ^^^
  (if i.val.testBit 3 then 96 else 0) ^^^
  (if i.val.testBit 4 then 400 else 0) ^^^
  (if i.val.testBit 5 then 656 else 0)

private theorem mask_lt : ∀ i : Fin 64, mask i < 2048 := by decide +kernel

private def xorIndex (i j : Fin 64) : Fin 64 :=
  ⟨i.val ^^^ j.val, Nat.xor_lt_two_pow (n := 6) i.isLt j.isLt⟩

private theorem mask_xor : ∀ i j : Fin 64, mask (xorIndex i j) = mask i ^^^ mask j := by
  decide +kernel

private theorem mask_injective : Function.Injective mask := by decide +kernel

private theorem mask_pure : ∀ i : Fin 64, i ≠ 0 →
    OrbitData.inPairOrbit (mask i) = true := by decide +kernel

private def element (i : Fin 64) : Model :=
  ((maskValue matrixA_mul_self matrixB_pow_four (mask i) : M) : Model)

private theorem element_zero : element 0 = 1 :=
  congrArg (fun x : K => ((x : M) : Model))
    (maskValue_zero matrixA_mul_self matrixB_pow_four)

private theorem element_xor (i j : Fin 64) :
    element (xorIndex i j) = element i * element j := by
  unfold element
  rw [mask_xor]
  exact congrArg (fun x : K => ((x : M) : Model))
    (maskValue_xor matrixA_mul_self matrixB_pow_four (mask i) (mask j))

private theorem element_inv (i : Fin 64) : (element i)⁻¹ = element i := by
  apply inv_eq_of_mul_eq_one_right
  rw [←element_xor]
  have h : xorIndex i i = 0 := by apply Fin.ext; exact Nat.xor_self _
  rw [h,element_zero]

private theorem element_injective : Function.Injective element := by
  intro i j h
  apply mask_injective
  have hh := maskValue_injective (a₁ := ⟨mask i,mask_lt i⟩)
    (a₂ := ⟨mask j,mask_lt j⟩) (Subtype.ext (Subtype.ext h))
  exact congrArg Fin.val hh

private def U : Subgroup Model where
  carrier := Set.range element
  one_mem' := ⟨0,element_zero⟩
  mul_mem' := by rintro _ _ ⟨i,rfl⟩ ⟨j,rfl⟩; exact ⟨xorIndex i j,element_xor i j⟩
  inv_mem' := by rintro _ ⟨i,rfl⟩; exact ⟨i,(element_inv i).symm⟩

private theorem card_U : Nat.card U = 64 := by
  change Nat.card (Set.range element) = 64
  rw [←Nat.card_congr (Equiv.ofInjective element element_injective)]
  exact Nat.card_fin 64

private theorem elementary_U : IsElementaryAbelian 2 U := by
  let : IsElementaryAbelian 2 K := LocalStructure.localKernel_elementary
    matrixA_mul_self matrixB_pow_four
  let E := K.map M.subtype
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  apply IsElementaryAbelian.of_le (show U ≤ E from ?_)
  rintro _ ⟨i,rfl⟩
  exact ⟨maskValue matrixA_mul_self matrixB_pow_four (mask i),
    (maskValue matrixA_mul_self matrixB_pow_four (mask i)).property,rfl⟩

private theorem pure_U : ∀ u ∈ U, u ≠ 1 → IsConj Janko4.a u := by
  rintro _ ⟨i,rfl⟩ hne
  have hi : i ≠ 0 := by intro h; exact hne (h ▸ element_zero)
  have hp := mask_isConj_pair ⟨mask i,mask_lt i⟩ (mask_pure i hi)
  have hp' := M.subtype.map_isConj hp
  obtain ⟨g,hg⟩ := Janko4.Simplicity.Max1Fusion.pair_fuses_first
    matrixA_mul_self matrixB_pow_four
  have ha : Janko4.Simplicity.a matrixA_mul_self = Janko4.a := by
    apply Janko4.toMatrix_injective
    rfl
  rw [ha] at hg
  exact (isConj_iff.mpr ⟨g,hg.symm⟩).symm.trans hp'.symm

/-- An actual 2A-pure elementary subgroup of order64 in the native carrier. -/
theorem exists_pure_sixtyFour :
    ∃ E : Subgroup Model, IsElementaryAbelian 2 E ∧ Nat.card E = 64 ∧
      ∀ u ∈ E, u ≠ 1 → IsConj Janko4.a u :=
  ⟨U,elementary_U,card_U,pure_U⟩

/-- A blanket order bound below64 cannot follow from native 2A purity alone. -/
theorem not_pure_card_lt_sixtyFour :
    ¬ (∀ E : Subgroup Model, IsElementaryAbelian 2 E →
      (∀ u ∈ E, u ≠ 1 → IsConj Janko4.a u) → Nat.card E < 64) := by
  intro h
  have hb := h U elementary_U pure_U
  rw [card_U] at hb
  exact (lt_irrefl 64) hb

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.PureSixtyFour
