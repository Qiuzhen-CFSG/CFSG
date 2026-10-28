module

public import Theory.AlgebraicGroup.Parabolic.InvariantLeviGeometry.Classification.AlignedDefs
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy

/-!
# Classification after the geometric BN-pair comparison

These are conditional assembly lemmas. The aligned Tits system and its
comparison with the literal root-generated subgroups must still be constructed.
The abstract classification theorem yields uniqueness and order reflection;
Borel conjugacy transfers the standard result to every algebraic parabolic.

Source: GLS3, Theorem 1.13.2. The separate endpoint module already discharges
ambient root generation using the allowed earlier Bruhat and rank-one inputs.
-/

namespace Theory.AlgebraicGroup.InvariantLeviGeometry.Classification

open BorelIntersectionGeometry.RankOneGeometry
universe u
variable {k : Type u} [Field k]
  {K : Variety k} [AlgebraicGroup K]
  {S : StandardParabolicRelativeRootSetup K}
  {hpositive : S.positiveRoots = S.D.positive}
  {M : SimpleRootMarkings S.D S.positiveRoots}

namespace AlignedTitsSystem

variable (A : AlignedTitsSystem S hpositive M)

/-- Pull the abstract simple indices back to the actual simple roots. -/
@[expose] public def rootIndices (H : Subgroup (Variety.Point K)) : Set S.D.Root :=
  {a | ∃ ha : a ∈ S.D.simple,
    (A.simple ⟨a, ha⟩).val ∈ A.system.simpleIndices H}

public theorem rootIndices_subset (H : Subgroup (Variety.Point K)) :
    A.rootIndices H ⊆ S.D.simple := by
  rintro a ⟨ha, _⟩
  exact ha

public theorem simpleIndices_rootIndices (H : Subgroup (Variety.Point K)) :
    A.simpleIndices (A.rootIndices H) = A.system.simpleIndices H := by
  ext s
  constructor
  · rintro ⟨i, ⟨hi, hs⟩, rfl⟩
    exact hs
  · intro hs
    let ss : A.system.S := ⟨s, A.system.simpleIndices_subset H hs⟩
    refine ⟨A.simple.symm ss, ?_, ?_⟩
    · refine ⟨(A.simple.symm ss).property, ?_⟩
      change (A.simple (A.simple.symm ss)).val ∈ A.system.simpleIndices H
      simpa only [Equiv.apply_symm_apply] using hs
    · exact congrArg Subtype.val (A.simple.apply_symm_apply ss)

public theorem standard_classification_eq
    (H : Subgroup (Variety.Point K)) (hB : S.B.toSubgroup ≤ H) :
    H = A.standard (A.rootIndices H) := by
  change H = A.system.standardParabolic (A.simpleIndices (A.rootIndices H))
  rw [A.simpleIndices_rootIndices]
  apply A.system.subgroup_eq_standardParabolic_simpleIndices
  simpa only [A.borel_eq] using hB

variable [IsAlgClosed k]

public theorem rootParabolic_eq_iff_of_comparison
    (hcompare : ∀ J, J ⊆ S.D.simple →
      (rootParabolic S J).toSubgroup = A.standard J)
    {J J' : Set S.D.Root} (hJ : J ⊆ S.D.simple) (hJ' : J' ⊆ S.D.simple) :
    rootParabolic S J = rootParabolic S J' ↔ J = J' := by
  constructor
  · intro h
    have h' := congrArg (fun F : ClosedSubgroup K => F.toSubgroup) h
    rw [hcompare J hJ, hcompare J' hJ'] at h'
    exact Set.Subset.antisymm
      ((A.standard_le_iff hJ hJ').mp h'.le)
      ((A.standard_le_iff hJ' hJ).mp h'.ge)
  · rintro rfl
    rfl

/-- Every closed overgroup of the positive Borel has a unique actual simple
root subset, conditional on the geometric root-group comparison. -/
public theorem classification_of_comparison
    (hcompare : ∀ J, J ⊆ S.D.simple →
      (rootParabolic S J).toSubgroup = A.standard J)
    (H : ClosedSubgroup K) (hB : S.B ≤ H) :
    ∃! J : Set S.D.Root, J ⊆ S.D.simple ∧ H = rootParabolic S J := by
  let J := A.rootIndices H.toSubgroup
  have hJ : J ⊆ S.D.simple := A.rootIndices_subset _
  have hH : H = rootParabolic S J := by
    apply SetLike.coe_injective
    change (H.toSubgroup : Set (Variety.Point K)) =
      ((rootParabolic S J).toSubgroup : Set (Variety.Point K))
    rw [hcompare J hJ, A.standard_classification_eq H.toSubgroup hB]
  refine ⟨J, ⟨hJ, hH⟩, ?_⟩
  rintro J' ⟨hJ', hH'⟩
  exact (A.rootParabolic_eq_iff_of_comparison hcompare hJ' hJ).mp (hH'.symm.trans hH)

/-- The core BN-pair normalizer calculation applies to the literal closed
parabolic after comparison. -/
public theorem rootParabolic_normalizer_of_comparison
    (hcompare : ∀ J, J ⊆ S.D.simple →
      (rootParabolic S J).toSubgroup = A.standard J)
    {J : Set S.D.Root} (hJ : J ⊆ S.D.simple) :
    (rootParabolic S J).normalizer = rootParabolic S J := by
  apply SetLike.coe_injective
  change (Subgroup.normalizer ((rootParabolic S J).toSubgroup : Set (Variety.Point K)) :
      Set (Variety.Point K)) = ((rootParabolic S J).toSubgroup : Set (Variety.Point K))
  rw [hcompare J hJ]
  exact congrArg (fun H : Subgroup (Variety.Point K) => (H : Set (Variety.Point K)))
    (A.system.standardParabolic_normalizer_eq (A.simpleIndices_subset J))

/-- Borel conjugacy gives ambient conjugate classification, using the literal
closed-subgroup conjugation convention `g P g⁻¹`. -/
public theorem conjugate_classification_of_comparison
    (hB : IsBorelOfPositiveSystem S.D S.positiveRoots S.B)
    (hcompare : ∀ J, J ⊆ S.D.simple →
      (rootParabolic S J).toSubgroup = A.standard J)
    (H : ClosedSubgroup K) (hH : IsParabolicSubgroup H) :
    ∃ J ⊆ S.D.simple, ∃ g : Variety.Point K,
      H = (rootParabolic S J).conjugate g := by
  obtain ⟨B, hBorel, hBH⟩ := hH
  obtain ⟨g, rfl⟩ := BorelGeometricConjugacy.conjugacy hB.borel hBorel
  have hle : S.B ≤ H.conjugate g⁻¹ := by
    intro x hx
    change x ∈ S.B.toSubgroup at hx
    apply (H.mem_conjugate_iff g⁻¹ x).mpr
    simp only [inv_inv]
    apply hBH
    apply (S.B.mem_conjugate_iff g (g * x * g⁻¹)).mpr
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hx
  obtain ⟨J, ⟨hJ, heq⟩, _⟩ := A.classification_of_comparison hcompare
    (H.conjugate g⁻¹) hle
  refine ⟨J, hJ, g, ?_⟩
  have h := congrArg (fun F : ClosedSubgroup K => F.conjugate g) heq
  simpa only [ClosedSubgroup.conjugate_conjugate, mul_inv_cancel,
    ClosedSubgroup.conjugate_one] using h

/-- Conjugate classification transfers self-normalization to every algebraic
parabolic, still with the root-group comparison premise explicit. -/
public theorem parabolic_normalizer_of_comparison
    (hB : IsBorelOfPositiveSystem S.D S.positiveRoots S.B)
    (hcompare : ∀ J, J ⊆ S.D.simple →
      (rootParabolic S J).toSubgroup = A.standard J)
    (H : ClosedSubgroup K) (hH : IsParabolicSubgroup H) :
    H.normalizer = H := by
  obtain ⟨J, hJ, g, rfl⟩ := A.conjugate_classification_of_comparison hB hcompare H hH
  have hn := congrArg (fun F : ClosedSubgroup K => F.toSubgroup)
    (A.rootParabolic_normalizer_of_comparison hcompare hJ)
  apply SetLike.coe_injective
  change (Subgroup.normalizer
      ((rootParabolic S J).toSubgroup.comap (MulAut.conj g⁻¹).toMonoidHom :
        Set (Variety.Point K)) :
      Set (Variety.Point K)) =
    ((rootParabolic S J).toSubgroup.comap (MulAut.conj g⁻¹).toMonoidHom :
      Set (Variety.Point K))
  rw [← Subgroup.comap_normalizer_eq_of_surjective _ (MulAut.conj g⁻¹).surjective]
  rw [show Subgroup.normalizer ((rootParabolic S J).toSubgroup : Set (Variety.Point K)) =
    (rootParabolic S J).toSubgroup from hn]

end AlignedTitsSystem
end Theory.AlgebraicGroup.InvariantLeviGeometry.Classification
