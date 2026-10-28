module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Idempotent Trace

For a finite group, the trace of left multiplication followed by right
multiplication by a central element is the group order times its inverse
coefficient. Constancy of central coefficients on conjugacy classes makes
each diagonal entry equal. For an endomorphism commuting with an idempotent,
the image/kernel decomposition identifies the projected trace with the trace
on the image. The required summands are free over a local ring whenever the
ambient module is finite projective.

These results identify the coefficient detected by the central-idempotent
right-ideal representation.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/CentralIdempotentSupport.lean` (revision `c3503435`).
-/

public section

noncomputable section

open scoped BigOperators

open Module CategoryTheory

namespace ModularBlock.CentralIdempotentSupport

universe u v w

attribute [local instance] Fintype.ofFinite

/-- The coefficients of a central group-algebra element are constant on
conjugacy classes. -/
theorem coeff_conj_eq_of_mem_center
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (e : MonoidAlgebra R G) (he : e ∈ Set.center (MonoidAlgebra R G))
    (x y : G) :
    e.coeff (x * y * x⁻¹) = e.coeff y := by
  have hcomm := Semigroup.mem_center_iff.mp he (MonoidAlgebra.of R G x)
  have h := congrArg (fun z : MonoidAlgebra R G ↦ z.coeff (x * y)) hcomm
  simpa [MonoidAlgebra.of_apply, mul_assoc] using h.symm

/-- The trace of `x ↦ g * x * e` on the regular module is the group order
times the coefficient of `g⁻¹` in the central element `e`. -/
theorem trace_mulLeft_comp_mulRight
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (e : MonoidAlgebra R G) (he : e ∈ Set.center (MonoidAlgebra R G))
    (g : G) :
    LinearMap.trace R (MonoidAlgebra R G)
        ((LinearMap.mulLeft R (MonoidAlgebra.of R G g)).comp
          (LinearMap.mulRight R e)) =
      (Nat.card G : R) * e.coeff g⁻¹ := by
  classical
  let b : Basis G R (MonoidAlgebra R G) := MonoidAlgebra.basis _ _
  rw [LinearMap.trace_eq_matrix_trace R b, Matrix.trace]
  have hdiag : ∀ x : G,
      ((LinearMap.toMatrix b b)
        ((LinearMap.mulLeft R (MonoidAlgebra.of R G g)).comp
          (LinearMap.mulRight R e))).diag x = e.coeff g⁻¹ := by
    intro x
    simp only [Matrix.diag_apply, LinearMap.toMatrix_apply,
      LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    change (MonoidAlgebra.single g 1 *
      (MonoidAlgebra.single x 1 * e) : MonoidAlgebra R G).coeff x = e.coeff g⁻¹
    rw [← mul_assoc, MonoidAlgebra.single_mul_single]
    simp only [one_mul]
    rw [MonoidAlgebra.coeff_single_mul_apply]
    simpa [mul_assoc] using
      coeff_conj_eq_of_mem_center e he x⁻¹ g⁻¹
  simp_rw [hdiag]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  congr 1
  exact congrArg (fun n : ℕ ↦ (n : R))
    (Fintype.card_eq_nat_card : Fintype.card G = Nat.card G)

/-- If `p` is an idempotent commuting with `f`, the trace of `f ∘ p` is
the trace of `f` on the image of `p`. -/
theorem trace_comp_idempotent_eq_trace_range
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (p f : M →ₗ[R] M) (hp : IsIdempotentElem p)
    [Module.Free R (LinearMap.range p)]
    [Module.Finite R (LinearMap.range p)]
    [Module.Free R (LinearMap.ker p)]
    [Module.Finite R (LinearMap.ker p)]
    (hcomm : f.comp p = p.comp f) :
    LinearMap.trace R M (f.comp p) =
      LinearMap.trace R (LinearMap.range p)
        (f.restrict (by
          rintro _ ⟨x, rfl⟩
          refine ⟨f x, ?_⟩
          simpa [LinearMap.comp_apply] using
            congrArg (fun q : M →ₗ[R] M ↦ q x) hcomm.symm)) := by
  let hmap : LinearMap.range p ≤ (LinearMap.range p).comap f := by
    rintro _ ⟨x, rfl⟩
    refine ⟨f x, ?_⟩
    simpa [LinearMap.comp_apply] using
      congrArg (fun q : M →ₗ[R] M ↦ q x) hcomm.symm
  let fp : LinearMap.range p →ₗ[R] LinearMap.range p := f.restrict hmap
  let E := (LinearMap.range p).prodEquivOfIsCompl (LinearMap.ker p)
    (LinearMap.IsIdempotentElem.isCompl hp)
  have hconj : E.symm.conj (f.comp p) = LinearMap.prodMap fp 0 := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    apply E.injective
    simp only [LinearEquiv.conj_apply_apply, LinearEquiv.apply_symm_apply,
      LinearMap.prodMap_apply, E, fp]
    change f (p (x + y)) = f x + 0
    rw [map_add,
      (LinearMap.IsIdempotentElem.isProj_range p hp).map_id x x.2,
      LinearMap.mem_ker.mp y.2]
    simp
  calc
    LinearMap.trace R M (f.comp p) =
        LinearMap.trace R (LinearMap.range p × LinearMap.ker p)
          (E.symm.conj (f.comp p)) := by
            symm
            exact LinearMap.trace_conj' (f.comp p) E.symm
    _ = LinearMap.trace R (LinearMap.range p × LinearMap.ker p)
          (LinearMap.prodMap fp 0) := by rw [hconj]
    _ = LinearMap.trace R (LinearMap.range p) fp := by
      rw [LinearMap.trace_prodMap']
      simp

/-- The range of an idempotent on a projective module is projective. -/
theorem projective_range_of_isIdempotentElem
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Projective R M]
    (p : M →ₗ[R] M) (hp : IsIdempotentElem p) :
    Module.Projective R (LinearMap.range p) := by
  let hproj := LinearMap.IsIdempotentElem.isProj_range p hp
  apply Module.Projective.of_split (LinearMap.range p).subtype hproj.codRestrict
  ext x
  simp [LinearMap.comp_apply]

/-- Over a local ring, the image of an idempotent on a finite projective
module is free. -/
theorem free_range_of_isIdempotentElem_of_isLocalRing
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Projective R M] [Module.Finite R M]
    (p : M →ₗ[R] M) (hp : IsIdempotentElem p) :
    Module.Free R (LinearMap.range p) := by
  let : Module.Projective R (LinearMap.range p) :=
    projective_range_of_isIdempotentElem p hp
  exact Module.free_of_flat_of_isLocalRing

/-- Over a local ring, the kernel of an idempotent on a finite projective
module is free as well. -/
theorem free_ker_of_isIdempotentElem_of_isLocalRing
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Projective R M] [Module.Finite R M]
    (p : M →ₗ[R] M) (hp : IsIdempotentElem p) :
    Module.Free R (LinearMap.ker p) := by
  rw [LinearMap.IsIdempotentElem.ker_eq_range hp]
  exact free_range_of_isIdempotentElem_of_isLocalRing
    (LinearMap.id - p) hp.one_sub

end ModularBlock.CentralIdempotentSupport

