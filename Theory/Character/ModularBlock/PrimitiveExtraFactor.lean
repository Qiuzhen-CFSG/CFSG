module

public import Theory.Character.ModularBlock.PrincipalAugmentationOrthogonality
public import Theory.Character.ModularBlock.FiniteFieldPrimitivity

/-!
# Primitive factors of augmentation-zero Brauer idempotents

A nonzero central idempotent of augmentation zero lying below a direct
principal Brauer image contains a primitive extra factor. Finite-ring
central-idempotent descent supplies a primitive subfactor. Its augmentation
is zero and its ambient factor identity follows by associativity. Local
principal primitivity makes it orthogonal to the compatible local selector,
so subtraction identifies it as a factor of the extra Brauer complement.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/BrauerThirdMain.lean` (revision `c3503435`).
-/

public section

noncomputable section

namespace ModularBlock.BrauerThirdMain

open ModularBlock PrincipalBlockConstruction

universe v

attribute [local instance] Fintype.ofFinite

set_option linter.unusedVariables false in
/-- A nonzero central idempotent of augmentation zero under a direct Brauer
image contains a primitive extra obstruction. -/
theorem exists_primitiveExtraFactor_of_centralIdempotent
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q)
    (g : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)))
    (hgCenter : g ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer (Q : Set G))))
    (hgIdem : IsIdempotentElem g)
    (hgNe : g ≠ 0)
    (hgAug : groupAlgebraAugmentation
      (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)) g = 0)
    (hgFactor : g * DefectSupport.subgroupCentralizerRestriction
      (BrauerBlockReduction.principalResidueField d) Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d) = g) :
    ∃ b : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
        (Subgroup.centralizer (Q : Set G)),
      IsCentrallyPrimitive b ∧
        groupAlgebraAugmentation
            (BrauerBlockReduction.principalResidueField d)
            (Subgroup.centralizer (Q : Set G)) b = 0 ∧
        b * SubgroupPrincipalBrauer.extraBrauerFactor d Q = b := by
  let K := BrauerBlockReduction.principalResidueField d
  let C := Subgroup.centralizer (Q : Set G)
  let A := MonoidAlgebra K C
  let : Finite K := FiniteFieldPrimitivity.principalResidueField_finite d
  let : Fintype K := Fintype.ofFinite K
  let : Fintype C := Fintype.ofFinite C
  let : DecidableEq C := Classical.decEq C
  let : Finite A := by
    exact Finite.of_injective MonoidAlgebra.coeff MonoidAlgebra.coeff_injective
  have hmap :
      (Subring.subtype (Subring.center A)) ⟨g, hgCenter⟩ ≠ 0 := by
    simpa [A, K, C] using hgNe
  obtain ⟨bCI, hbPrimitive, hbFactor, _hbMap⟩ :=
    CentralPrimitiveExistence.exists_isCentrallyPrimitive_factor_map_ne_zero
      (A := A) (B := A) (Subring.subtype (Subring.center A)) g
      hgCenter hgIdem hmap
  let b : A := bCI.val
  have hbAug : groupAlgebraAugmentation K C b = 0 := by
    have h := congrArg (groupAlgebraAugmentation K C) hbFactor
    rw [map_mul, hgAug, mul_zero] at h
    exact h.symm
  have hbAmbient : b * DefectSupport.subgroupCentralizerRestriction K Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d) = b := by
    calc
      b * DefectSupport.subgroupCentralizerRestriction K Q
            (BrauerBlockReduction.reducedPrincipalBlockElement d) =
          (b * g) * DefectSupport.subgroupCentralizerRestriction K Q
            (BrauerBlockReduction.reducedPrincipalBlockElement d) := by
              rw [hbFactor]
      _ = b * (g * DefectSupport.subgroupCentralizerRestriction K Q
            (BrauerBlockReduction.reducedPrincipalBlockElement d)) := by
              rw [mul_assoc]
      _ = b * g := by rw [hgFactor]
      _ = b := hbFactor
  have hbLocal : b *
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d C = 0 :=
    PrincipalAugmentationOrthogonality.primitiveAugmentationZero_mul_localPrincipal_eq_zero
      d C b hbPrimitive hbAug
  have hbExtra : b * SubgroupPrincipalBrauer.extraBrauerFactor d Q = b := by
    rw [SubgroupPrincipalBrauer.extraBrauerFactor, mul_sub]
    change b * DefectSupport.subgroupCentralizerRestriction K Q
          (BrauerBlockReduction.reducedPrincipalBlockElement d) -
        b * CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d C = b
    rw [hbAmbient, hbLocal, sub_zero]
  exact ⟨b, by simpa [b, A, K, C] using hbPrimitive,
    by simpa [b, A, K, C] using hbAug,
    by simpa [b, A, K, C] using hbExtra⟩

end ModularBlock.BrauerThirdMain

