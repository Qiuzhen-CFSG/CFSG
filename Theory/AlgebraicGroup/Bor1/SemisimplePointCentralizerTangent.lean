module

public import Theory.AlgebraicGroup.Bor1.SemisimpleInfinitesimalStabilizer

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-!
This module packages the tangent-space formula from GLS Bor1, Proposition
9.1.  For a semisimple point `s`, the identity tangent of the centralizer of
the Zariski closure of `s`'s cyclic subgroup is exactly the fixed subspace of
the tangent conjugation action of `s`.

The substantive fixed-to-centralizer inclusion is supplied by the
semisimple infinitesimal stabilizer theorem.  Its proof uses semisimplicity on
the coordinate algebra and the fixed-locus cotangent ideal, rather than an
assumed smoothness statement.  Conversely, the cyclic closure is abelian, so
`s` belongs to its centralizer; naturality of the inclusion differential then
reduces conjugation of a centralizer tangent to the identity conjugation
action inside the centralizer.
-/

private lemma identityTangentConjugationLinearMap_eq_id_of_central
    {Q : Variety k} [AlgebraicGroup Q]
    (q : Variety.Point Q)
    (hq : ∀ x : Variety.Point Q, Commute q x) :
    identityTangentConjugationLinearMap Q q = LinearMap.id := by
  apply LinearMap.ext
  intro D
  apply Derivation.ext
  intro p
  rw [LinearMap.id_apply, identityTangentConjugationLinearMap_apply]
  apply congrArg D
  apply Variety.PolynomialFunction.ext
  intro x
  change p (q * x * q⁻¹) = p x
  congr 1
  calc
    q * x * q⁻¹ = (x * q) * q⁻¹ := by rw [(hq x).eq]
    _ = x := by simp

/-- The tangent space of the centralizer of a semisimple point's cyclic
closure is the fixed subspace of its tangent conjugation action. -/
public theorem identityTangent_semisimplePointCentralizer_range_eq_fixed
    (G : Variety k) [AlgebraicGroup G]
    (s : Variety.Point G) (hs : IsSemisimpleElement G s) :
    let C := (subgroupZariskiClosure G (Subgroup.zpowers s)).centralizer
    LinearMap.range (identityTangentMorphismLinearMap C.inclusion) =
      LinearMap.ker
        (identityTangentConjugationLinearMap G s - LinearMap.id) := by
  let S := subgroupZariskiClosure G (Subgroup.zpowers s)
  let C := S.centralizer
  have hsS : s ∈ S.toSubgroup :=
    subset_closure (Subgroup.mem_zpowers s)
  have hsC : s ∈ C.toSubgroup := by
    change s ∈ Subgroup.centralizer (S.toSubgroup : Set (Variety.Point G))
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (subgroupZariskiClosure_zpowers_isAbelian s s x hsS hx).symm
  let sC : Variety.Point C.carrierVariety := C.pointEquiv.symm ⟨s, hsC⟩
  have hsCval : C.includePoint sC = s := by
    change (C.pointEquiv sC).val = s
    simp [sC]
  have hsCcentral : ∀ x : Variety.Point C.carrierVariety, Commute sC x := by
    intro x
    apply C.inclusion_injective
    change s * C.includePoint x = C.includePoint x * s
    exact (Subgroup.mem_centralizer_iff.mp (C.pointEquiv x).property) s hsS
  apply le_antisymm
  · rintro D ⟨d, rfl⟩
    rw [LinearMap.mem_ker]
    change identityTangentConjugationLinearMap G s
        (identityTangentMorphismLinearMap C.inclusion d) -
      identityTangentMorphismLinearMap C.inclusion d = 0
    have hnat := LinearMap.congr_fun
      (identityTangentMorphismLinearMap_conjugation_naturality C.inclusion sC) d
    change identityTangentMorphismLinearMap C.inclusion
        (identityTangentConjugationLinearMap C.carrierVariety sC d) =
      identityTangentConjugationLinearMap G s
        (identityTangentMorphismLinearMap C.inclusion d) at hnat
    rw [← hnat, identityTangentConjugationLinearMap_eq_id_of_central sC hsCcentral]
    simp
  · intro D hD
    apply identityTangent_fixed_mem_semisimplePointCentralizer_range G s hs D
    rw [LinearMap.mem_ker] at hD
    change identityTangentConjugationLinearMap G s D - D = 0 at hD
    exact sub_eq_zero.mp hD

end Theory.AlgebraicGroup.Bor1
