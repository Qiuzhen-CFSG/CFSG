module
public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Bounds
public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.Representation.TensorInvolutionDisplacement
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# The two natural descent constituents for a moved A₅ pair

The first module is the binary restriction of the tensor of the two natural
SL₂(4) modules. The second twists just the second factor by Frobenius. Their
sum has binary dimension sixteen. Regrouping by the first natural coordinate
identifies the sum with an amplified natural action, so any intertwiner of a
nontrivial inner involution moves at least eight dimensions.

Source: Aschbacher–Smith, quasithin manuscript, D.3.5, pp.195–196. These
literal models support the separate source orbit and normalizer arguments.
-/

@[expose] public noncomputable section
open Module
open scoped TensorProduct
namespace Representation.AlternatingFiveMovedPair.Natural
open SL2FourNatural BinaryOffender BinaryOffender.NaturalTensor
abbrev Tensor := TensorSpace F
abbrev Space := Tensor × Tensor

def first : Representation (ZMod 2) (SL × SL) Tensor := binaryTensorAction F

def second : Representation (ZMod 2) (SL × SL) Tensor :=
  first.comp ((MulEquiv.refl SL).prodCongr slFrobenius).toMonoidHom

def action : Representation (ZMod 2) (SL × SL) Space := first.prod second

instance tensorFinite : FiniteDimensional (ZMod 2) Tensor := Module.Finite.trans F Tensor

lemma finrank_tensor : finrank (ZMod 2) Tensor = 8 :=
  NaturalTensor.finrank_tensor F (n := 2) (by rw [Nat.card_eq_fintype_card, card_field]; norm_num)

lemma finrank_space : finrank (ZMod 2) Space = 16 := by
  rw [Module.finrank_prod, finrank_tensor]

/-- Regroup the two descent summands by their first natural coordinate. -/
def firstCoordinates : Space ≃ₗ[ZMod 2] ((V × V) × (V × V)) :=
  (((tensorPairCoordinates F).prodCongr (tensorPairCoordinates F)).trans
    (LinearEquiv.prodProdProdComm F V V V V)).restrictScalars (ZMod 2)

lemma firstCoordinates_action (g : SL) (v : Space) :
    firstCoordinates (action (g, 1) v) = amplifiedNatural g (firstCoordinates v) := by
  have hs : slFrobenius (1 : SL) = 1 := map_one slFrobenius
  change (((tensorPairCoordinates F (first (g, 1) v.1)).1,
      (tensorPairCoordinates F (first (g, slFrobenius 1) v.2)).1),
    ((tensorPairCoordinates F (first (g, 1) v.1)).2,
      (tensorPairCoordinates F (first (g, slFrobenius 1) v.2)).2)) = _
  rw [hs]
  change (((tensorPairCoordinates F (tensorAction F (g, 1) v.1)).1,
      (tensorPairCoordinates F (tensorAction F (g, 1) v.2)).1),
    ((tensorPairCoordinates F (tensorAction F (g, 1) v.1)).2,
      (tensorPairCoordinates F (tensorAction F (g, 1) v.2)).2)) = _
  rw [tensorPairCoordinates_first, tensorPairCoordinates_first]
  rfl

/-- The first component has multiplicity four over the four-element field. -/
theorem first_inner_intertwiner_bound (T : Module.End (ZMod 2) Space)
    (hTi : Function.Injective T) (r : SL) (hr : r * r = 1) (hne : r ≠ 1)
    (hT : ∀ g v, T (action (g, 1) v) = action (r * g * r⁻¹, 1) (T v)) :
    8 ≤ operatorFixedCodim T := by
  let ρ := action.comp (MonoidHom.inl SL SL)
  have hh := inner_bound_of_realization ρ firstCoordinates
    firstCoordinates_action T hTi r hr hne hT
  have hd : finrank (ZMod 2) (V × V) = 8 := by
    simp only [Module.finrank_prod, V, Module.finrank_pi_fintype, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [NaturalTensor.finrank_field F (n := 2) (by rw [Nat.card_eq_fintype_card, card_field]; norm_num)]
  rwa [hd] at hh

end Representation.AlternatingFiveMovedPair.Natural
