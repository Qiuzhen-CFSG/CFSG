module
public import Theory.Representation.OrthogonalFourPlusMatrix.NormalizerSingularity

/-!
# The full moved point of a low-rank orthogonal involution

A rank-two involution in the binary determinant normalizer is linear over
F₄ with a one-dimensional field displacement space. Its nonzero moved
vectors are nonsingular. Hence its whole binary displacement space is the
restriction of an actual nonsingular F₄-point.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1057,
refs/quasithin.pdf. The original critical actor application is in
LocalReduction.BinaryMovedPoint.
-/

public noncomputable section
open Module Matrix Subgroup
open Representation.BinaryOffender Representation.BinaryOffender.NaturalTensor
namespace ClassicalOrthogonal.FourPlusMatrix.Binary

/-- A rank-two involution in the full binary normalizer moves one entire
nonsingular coefficient-field point. -/
theorem rank_two_involution_moved_point (t : linearNormalizer action)
    (ht2 : t ^ 2 = 1) (hr : operatorFixedCodim t.val.val = 2) :
    ∃ v : V, v.det ≠ 0 ∧
      LinearMap.range (t.val.val - LinearMap.id) =
        (Submodule.span F ({v} : Set V)).restrictScalars (ZMod 2) := by
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv t.val
  have he : e ∈ normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)) :=
    normalizer_linearEquiv_mem t
  have hne : e ≠ 1 := by
    intro hz
    have hh : t.val.val = LinearMap.id := congrArg LinearEquiv.toLinearMap hz
    change Module.finrank (ZMod 2) (t.val.val - LinearMap.id).range = 2 at hr
    rw [hh,sub_self,LinearMap.range_zero,finrank_bot] at hr
    omega
  obtain ⟨u,hu,hru,_⟩ := low_rank_nonidentity e he hr.le hne
  obtain ⟨x,hx⟩ : ∃ x : V, e x ≠ x := by
    by_contra! hh
    exact hne (LinearEquiv.ext hh)
  let v := e x - x
  have hv : v ≠ 0 := sub_ne_zero.mpr hx
  have hvu : v ∈ (u.toLinearMap - LinearMap.id).range := by
    refine ⟨x,?_⟩
    change u x - x = e x - x
    exact congrArg (fun f : V ≃ₗ[ZMod 2] V => f x - x) hu
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hru hvu hv
  have he2 : e ^ 2 = 1 := by
    apply LinearEquiv.ext
    intro w
    exact congrArg (fun b : linearNormalizer action => b.val.val w) ht2
  have hvn : v.det ≠ 0 := by
    intro hz
    exact low_rank_involution_singular_not_mem_displacement e he hr.le he2 v hv hz ⟨x,rfl⟩
  refine ⟨v,hvn,?_⟩
  rw [←hspan]
  ext w
  change (∃ x : V, t.val.val x - x = w) ↔
    ∃ x : V, u x - x = w
  have hh (x : V) : u x = t.val.val x := congrArg (fun f : V ≃ₗ[ZMod 2] V => f x) hu
  simp only [hh]

end ClassicalOrthogonal.FourPlusMatrix.Binary
