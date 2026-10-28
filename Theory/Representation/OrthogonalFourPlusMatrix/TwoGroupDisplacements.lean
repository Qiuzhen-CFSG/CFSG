module
public import Theory.LinearAlgebra.QuadraticTwoGroupTransvections
public import Theory.Representation.OrthogonalFourPlusMatrix.NormalizerSingularity

/-!
# Low-rank orthogonal actors in a common two-subgroup

Binary rank at most two makes an involution in the determinant normalizer
linear over F₄ and of field rank at most one. The rank-one quadratic
isometry theorem then shows that two such involutions with two-power
product fix each other's full binary displacement spaces.

Source application: the normal span of the critical actor in
Aschbacher–Smith, proof of 14.7.32, printed p.1058, refs/quasithin.pdf.
-/

public noncomputable section
open Module

open Subgroup Representation.BinaryOffender Representation.BinaryOffender.NaturalTensor
namespace ClassicalOrthogonal.FourPlusMatrix.Binary

/-- Low-rank involutions in a common two-subgroup fix each other's full
binary displacement spaces. -/
theorem low_rank_two_power_fixes_displacement
    (s t : V ≃ₗ[ZMod 2] V)
    (hs : s ∈ normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)))
    (ht : t ∈ normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)))
    (hs2 : s*s = 1) (ht2 : t*t = 1)
    (hrs : finrank (ZMod 2) (s.toLinearMap - LinearMap.id).range ≤ 2)
    (hrt : finrank (ZMod 2) (t.toLinearMap - LinearMap.id).range ≤ 2)
    (hn : ∃ n : ℕ, (s*t)^(2^n) = 1) :
    ∀ z ∈ (t.toLinearMap - LinearMap.id).range, s z = z := by
  obtain ⟨s',hs'⟩ := low_rank_field_equiv s hs hrs
  obtain ⟨t',ht'⟩ := low_rank_field_equiv t ht hrt
  let r : (V ≃ₗ[F] V) →* (V ≃ₗ[ZMod 2] V) := {
    toFun := LinearEquiv.restrictScalars (ZMod 2)
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hrs' : finrank F (s'.toLinearMap - LinearMap.id).range ≤ 1 := by
    have hh := QuadraticForm.displacement_rank_restrictScalars (k := ZMod 2) s'
    rw [hs',finrank_field] at hh
    omega
  have hrt' : finrank F (t'.toLinearMap - LinearMap.id).range ≤ 1 := by
    have hh := QuadraticForm.displacement_rank_restrictScalars (k := ZMod 2) t'
    rw [ht',finrank_field] at hh
    omega
  have hs2' : s'*s' = 1 := by
    apply (LinearEquiv.restrictScalars_injective (ZMod 2))
    change r (s'*s') = r 1
    rw [map_mul,map_one]
    change s'.restrictScalars (ZMod 2)*s'.restrictScalars (ZMod 2)=1
    rwa [hs']
  have ht2' : t'*t' = 1 := by
    apply (LinearEquiv.restrictScalars_injective (ZMod 2))
    change r (t'*t') = r 1
    rw [map_mul,map_one]
    change t'.restrictScalars (ZMod 2)*t'.restrictScalars (ZMod 2)=1
    rwa [ht']
  have hnp : ∃ n : ℕ, (s'*t')^(2^n) = 1 := by
    obtain ⟨n,hn⟩ := hn
    refine ⟨n,?_⟩
    apply (LinearEquiv.restrictScalars_injective (ZMod 2))
    change r ((s'*t')^(2^n)) = r 1
    rw [map_pow,map_mul,map_one]
    change (s'.restrictScalars (ZMod 2)*t'.restrictScalars (ZMod 2))^(2^n)=1
    rwa [hs',ht']
  have hsd := field_involution_preserves_det s' (by rwa [hs'])
    (fun z => LinearEquiv.congr_fun hs2' z)
  have htd := field_involution_preserves_det t' (by rwa [ht'])
    (fun z => LinearEquiv.congr_fun ht2' z)
  have hf := QuadraticForm.rank_one_two_power_fixes_displacement
    determinantForm determinant_polar_separating s' t'
      (by simpa only [determinantForm_apply] using hsd)
      (by simpa only [determinantForm_apply] using htd) hs2' ht2' hrs' hrt' hnp
  intro z hz
  have hmem : z ∈ (t'.toLinearMap-LinearMap.id).range := by
    obtain ⟨x,hx⟩ := hz
    refine ⟨x,?_⟩
    change t' x-x=z
    have he := LinearEquiv.congr_fun ht' x
    change t' x=t x at he
    rw [he]
    exact hx
  have he := LinearEquiv.congr_fun hs' z
  exact he.symm.trans (hf z hmem)

end ClassicalOrthogonal.FourPlusMatrix.Binary
