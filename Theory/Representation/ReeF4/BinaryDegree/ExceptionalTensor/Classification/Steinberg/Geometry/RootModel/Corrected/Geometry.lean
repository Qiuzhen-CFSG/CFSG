module
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected.Data
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.TorusConjugacy
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.TorusConjugacy.Centralizer
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentLines
public import Theory.AlgebraicGroup.RootSubgroups.NormalizerMembership

/-!
# Remaining geometric boundary for the concrete F4 model

The checked matrix centralizer calculation proves maximality of the literal
split torus in characteristic two. If the known tangent summands span, every
nontrivial tangent weight is a literal inverse root weight. Differentiating any
one-parameter root subgroup then proves root exhaustiveness. This supplies the
remaining realization field; the tangent-spanning input remains explicit.

Source: GLS3 1.9.3--1.9.6. Tangent spanning has its separate geometric owner;
point generation alone is not used as a differential spanning argument.
-/

public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Theory.AlgebraicGroup.F4Chevalley
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
local instance geometryTorusGroup : AlgebraicGroup (splitTorus (k := F)).carrierVariety :=
  (splitTorus (k := F)).carrierAlgebraicGroup

/-- The split torus itself is maximal in characteristic two. -/
theorem splitTorus_isMaximal [CharP F 2] : IsMaximalTorus (splitTorus (k := F)) :=
  TorusConjugacy.splitTorus_isMaximal_of_matrix_centralizer
    TorusConjugacy.matrix_centralizer_eq_torusElement

/-- Tangent spanning excludes all further nontrivial root characters. -/
theorem tangentWeight_eq_rootWeight
    (hspan : (⨆ i, concreteTangentSummand (k := F) i) = ⊤)
    (χ : TorusWeight (splitTorus (k := F))) (hχ : χ ≠ 1)
    {v : IdentityPointDerivation (Carrier (k := F))}
    (hv : IsWeightVector (identityTangentRepresentation (Carrier (k := F)))
      splitTorus v χ⁻¹) : ∃ r : Root, χ = rootWeight r := by
  by_contra hn
  push Not at hn
  let p : TorusWeight (splitTorus (k := F)) →
      Submodule F (IdentityPointDerivation (Carrier (k := F))) :=
    weightSpace (identityTangentRepresentation (Carrier (k := F))) splitTorus
  have hnot : χ⁻¹ ∉ Set.range (concreteTangentWeight (k := F)) := by
    rintro ⟨i, hi⟩
    cases i with
    | none =>
      apply hχ
      simpa only [concreteTangentWeight, inv_one, inv_inv] using (congrArg Inv.inv hi.symm)
    | some r => exact hn r (inv_injective hi.symm)
  have hd : Disjoint (p χ⁻¹)
      (⨆ ψ ∈ Set.range (concreteTangentWeight (k := F)), p ψ) :=
    (weightSpace_iSupIndep (identityTangentRepresentation (Carrier (k := F)))
      (splitTorus (k := F))).disjoint_biSup hnot
  have hle : (⨆ i, concreteTangentSummand (k := F) i) ≤
      (⨆ ψ ∈ Set.range (concreteTangentWeight (k := F)), p ψ) := by
    apply iSup_le
    intro i
    exact (concreteTangentSummand_le_weightSpace i).trans
      (le_iSup_of_le (concreteTangentWeight i)
        (le_iSup_of_le ⟨i, rfl⟩ le_rfl))
  have hmem : v ∈ (⨆ ψ ∈ Set.range (concreteTangentWeight (k := F)), p ψ) := by
    apply hle
    rw [hspan]
    trivial
  exact hv.1 (Submodule.disjoint_def.mp hd v hv.2 hmem)

/-- Exhaustiveness of the literal root characters, conditional only on actual tangent spanning. -/
theorem rootWeight_range_of_tangent_span [CharP F 2]
    (hspan : (⨆ i, concreteTangentSummand (k := F) i) = ⊤) :
    Set.range (rootWeight (k := F)) = TorusRootSet (splitTorus (k := F)) := by
  apply Set.Subset.antisymm
  · rintro χ ⟨r, rfl⟩
    exact ⟨rootSubgroup r, rootSubgroup_package r⟩
  · rintro χ ⟨X, hX, hEq⟩
    have hne : χ ≠ 1 := hX.rootWeight_ne_one_of_centralizer_eq splitTorus_isSubtorus
      (TorusConjugacy.splitTorus_centralizer_eq_of_matrix_centralizer
        TorusConjugacy.matrix_centralizer_eq_torusElement) χ hEq
    let x := Classical.choice hX.2
    obtain ⟨r, hr⟩ := tangentWeight_eq_rootWeight hspan χ hne
      (oneParameterTangent_isWeightVector (splitTorus (k := F)) X x hEq)
    exact ⟨r, hr.symm⟩

/-- The actual standard-base model once the remaining tangent-spanning theorem is supplied. -/
@[expose] def modelOfTangentSpan [CharP F 2]
    (hspan : (⨆ i, concreteTangentSummand (k := F) i) = ⊤) :
    RootSystemModel typeF4RootPairingULift (Carrier (k := F)) :=
  model (rootWeight_range_of_tangent_span hspan) splitTorus_isMaximal

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected
