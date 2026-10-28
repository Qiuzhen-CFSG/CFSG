module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Triangular
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Cartan.Transfer
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Cartan.Matrices

/-!
# Cartan commutators of the actual rational root coefficients

The integral matrix identities lift through the injective differential of the
closed carrier inclusion. The differential of the arbitrary rational factor
then sends each root tangent to its actual first coefficient. Consequently,
opposite-root brackets lie in the span of simple Cartan commutators, and a
simple Cartan commutator brackets with every root coefficient by its coroot
pairing. These are operator identities on the whole factor; no highest-vector,
density, or span-invariance hypothesis is used.

Source: Steinberg, *Representations of Algebraic Groups* (1963), §§2, 4 and
11.1(1), DOI 10.1017/S0027763000011016.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
namespace NegativeCyclicity.SpanInvariance
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
local instance spanInvarianceCartanNeg : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
attribute [local instance] LieRing.ofAssociativeRing
open CartanTransfer CartanMatrices

private def simpleCartanTangent (i : Fin 4) :
    IdentityPointDerivation (F4Chevalley.Carrier (k := F)) :=
  ⁅rootTangent (F := F) (typeF4SimpleRootIndex i), rootTangent (F := F) (-typeF4SimpleRootIndex i)⁆

private theorem matrixDifferential_simpleCartan (i : Fin 4) :
    matrixDifferential (simpleCartanTangent (F := F) i) = specializedCartanMatrix i := by
  simp only [simpleCartanTangent, LieHom.map_lie, matrixDifferential_rootTangent,
    Ring.lie_def, specializedCartanMatrix, specializedRootMatrix]

/-- An opposite short-root bracket lies in the span of the four actual simple brackets. -/
theorem opposite_short_commutator_mem_cartan [CharP F 2] {B : AlgebraicFactor F}
    (p : RootExpansion B.action) (r : ShortPositiveRoot) :
    p.coeff r.val 1 * p.coeff (-r.val) 1 - p.coeff (-r.val) 1 * p.coeff r.val 1 ∈
      cartanOperators p := by
  obtain ⟨d, hd⟩ := exists_coefficient_lieHom p
  have himage : matrixDifferential (F := F) '' Set.range (simpleCartanTangent (F := F)) =
      Set.range (specializedCartanMatrix (F := F)) := by
    rw [← Set.range_comp]
    congr 1
    funext i
    exact matrixDifferential_simpleCartan i
  have hmatrix : matrixDifferential (F := F) ⁅rootTangent (F := F) r.val, rootTangent (F := F) (-r.val)⁆ ∈
      Submodule.span F (matrixDifferential (F := F) '' Set.range (simpleCartanTangent (F := F))) := by
    rw [himage, LieHom.map_lie, matrixDifferential_rootTangent,
      matrixDifferential_rootTangent, Ring.lie_def]
    exact specialized_opposite_mem_span r.val r.property.2
  have ht : ⁅rootTangent (F := F) r.val, rootTangent (F := F) (-r.val)⁆ ∈
      Submodule.span F (Set.range (simpleCartanTangent (F := F))) :=
    (Submodule.apply_mem_span_image_iff_mem_span
      (f := (matrixDifferential (F := F)).toLinearMap) matrixDifferential_injective).mp hmatrix
  have hle : Submodule.span F (Set.range (simpleCartanTangent (F := F))) ≤
      (cartanOperators p).comap d.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change d (simpleCartanTangent i) ∈ cartanOperators p
    simp only [simpleCartanTangent, LieHom.map_lie, hd, Ring.lie_def]
    exact Submodule.subset_span ⟨i, rfl⟩
  have h := hle ht
  change d ⁅rootTangent (F := F) r.val, rootTangent (F := F) (-r.val)⁆ ∈ cartanOperators p at h
  simpa only [LieHom.map_lie, hd, Ring.lie_def] using h

/-- Simple Cartan commutators act on every root coefficient by its coroot pairing. -/
theorem cartan_commutator_eq_pairing {B : AlgebraicFactor F}
    (p : RootExpansion B.action) (i : Fin 4) (s : F4Chevalley.Root) :
    cartanOperator p i * p.coeff s 1 - p.coeff s 1 * cartanOperator p i =
      (typeF4RootPairing.pairingIn ℤ s (typeF4SimpleRootIndex i) : F) • p.coeff s 1 := by
  obtain ⟨d, hd⟩ := exists_coefficient_lieHom p
  have ht : ⁅simpleCartanTangent (F := F) i, rootTangent (F := F) s⁆ =
      (typeF4RootPairing.pairingIn ℤ s (typeF4SimpleRootIndex i) : F) • rootTangent (F := F) s := by
    apply matrixDifferential_injective
    simp only [LieHom.map_lie, matrixDifferential_simpleCartan,
      matrixDifferential_rootTangent, map_smul, Ring.lie_def]
    exact specialized_cartan_bracket i s
  have h := congrArg d ht
  simpa only [simpleCartanTangent, LieHom.map_lie, hd, map_smul,
    Ring.lie_def, cartanOperator] using h

/-- Cartan commutators preserve the linear space of negative short coefficients. -/
theorem cartan_commutator_mem_negative [CharP F 2] {B : AlgebraicFactor F}
    (p : RootExpansion B.action) (i : Fin 4) (s : ShortNegativeRoot) :
    cartanOperator p i * p.coeff s.val 1 - p.coeff s.val 1 * cartanOperator p i ∈
      negativeOperators p := by
  rw [cartan_commutator_eq_pairing]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)

end
end NegativeCyclicity.SpanInvariance
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
