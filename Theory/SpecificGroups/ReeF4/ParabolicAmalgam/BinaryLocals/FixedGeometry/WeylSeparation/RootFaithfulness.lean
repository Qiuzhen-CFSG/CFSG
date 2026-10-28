module
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.WeylSeparation.Coordinates

/-!
# Faithfulness on the root vectors of the binary Ree representation

If an element fixes every root vector, restricted adjoint equivariance makes
it commute with each short simple root operator. Applying that operator to
the opposite root vector recovers its simple Cartan vector. Thus the element
fixes the entire short ideal, whose faithfulness is already proved for the
actual integral F₄ carrier. No simplicity assumption is used.

Source: the integral Geck representation and its short ideal in characteristic
two, as developed in `WordRelations.Faithfulness`.
-/

public section
noncomputable section
namespace ReeF4.Parabolics.Binary.FixedGeometry.WeylSeparation
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open WordRelations WordRelations.Faithfulness WordRelations.Faithfulness.Adjoint
open WordRelations.Faithfulness.RestrictedAdjoint
open scoped Matrix
private local instance rootFaithfulnessIndexNeg : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem cast_e_neg (i : typeF4RootPairing_base.support) :
    (eMatrix (P := typeF4RootPairing) i).map (Int.castRingHom (CoefficientField 0)) *ᵥ
      Pi.single (Sum.inr (-i.val)) 1 = Pi.single (Sum.inl i) 1 := by
  have h := congrArg (fun v : F4Chevalley.BasisIndex → ℤ =>
    (Int.castRingHom (CoefficientField 0)) ∘ v)
      (eMatrix_mulVec_v_neg (P := typeF4RootPairing) i)
  have hm (A : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex ℤ)
      (v : F4Chevalley.BasisIndex → ℤ) :
      (Int.castRingHom (CoefficientField 0)) ∘ (A *ᵥ v) =
        A.map (Int.castRingHom (CoefficientField 0)) *ᵥ
          ((Int.castRingHom (CoefficientField 0)) ∘ v) := by
    ext i
    exact (Int.castRingHom (CoefficientField 0)).map_mulVec A v i
  have hs (j : F4Chevalley.BasisIndex) :
      (Int.castRingHom (CoefficientField 0)) ∘ Pi.single j (1 : ℤ) = Pi.single j 1 := by
    classical
    ext x
    simp [Pi.single_apply]
  simpa only [hm, u, v, hs] using h

/-- Fixing every root vector forces a matrix in the actual Ree group to be one. -/
theorem eq_one_of_fixes_roots (n : Model 0)
    (hfix : ∀ r : F4Chevalley.Root,
      matrix n *ᵥ Pi.single (Sum.inr r) 1 = Pi.single (Sum.inr r) 1) : n = 1 := by
  let g : MatrixUnits 0 := (toSplitGroup 0 n).val
  have hg : g ∈ Subgroup.closure (Set.range
      (fun rt : F4Chevalley.Root × CoefficientField 0 => F4Chevalley.rootCurve rt.1 rt.2)) :=
    (toSplitGroup 0 n).property
  have heq := generated_equivariantOnShort 0 g hg
  have hcart (i : typeF4RootPairing_base.support) (hi : IsShortRoot i.val) :
      matrix n *ᵥ Pi.single (Sum.inl i) 1 = Pi.single (Sum.inl i) 1 := by
    have hE : (F4Chevalley.integralOperators.rootOperator i.val).map
        (Int.castRingHom (CoefficientField 0)) =
      (eMatrix (P := typeF4RootPairing) i).map (Int.castRingHom (CoefficientField 0)) :=
      congrArg (fun A : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex ℤ =>
        A.map (Int.castRingHom (CoefficientField 0))) (rootOperator_simple i)
    have hc := heq (Pi.single (Sum.inr i.val) 1) (shortSupported_single _ hi)
    change adjointMap 0 (matrix n *ᵥ Pi.single (Sum.inr i.val) 1) * matrix n =
      matrix n * adjointMap 0 (Pi.single (Sum.inr i.val) 1) at hc
    rw [hfix, adjointMap_root_single, hE] at hc
    have hh := congrArg (fun A : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex
      (CoefficientField 0) => A *ᵥ Pi.single (Sum.inr (-i.val)) 1) hc
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfix, cast_e_neg] at hh
    exact hh.symm
  have hg1 : g = 1 := eq_one_of_fixes_short_coordinates 0 g hg (by
    intro j hj
    cases j with
    | inr r => exact hfix r
    | inl i => exact hcart i hj)
  apply toSplitGroup_injective 0
  apply Subtype.ext
  simpa only [map_one, Subgroup.coe_one] using hg1

end ReeF4.Parabolics.Binary.FixedGeometry.WeylSeparation
