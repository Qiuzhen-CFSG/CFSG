module
public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Simultaneous density for a finite simple-module family

Over an algebraically closed field, any family of linear endomorphisms of
finitely many pairwise nonisomorphic finite-dimensional simple modules is
simultaneously realized by one element of their acting algebra. No
semisimplicity of the algebra or characteristic restriction is assumed.
This form of Jacobson density supplies trace-separating elements for the
linear independence of modular irreducible characters.

The product of the simple modules is semisimple. Schur's lemma makes each
endomorphism of this product diagonal with scalar diagonal entries: an
off-diagonal block would otherwise give an isomorphism between two distinct
simple modules. The product of the prescribed field-linear maps therefore
commutes with all algebra-linear endomorphisms. Mathlib's semisimple
`jacobson_density`, applied on a finite field-basis, realizes this product
by a single algebra element. The original module and scalar-tower instances
are retained throughout.
-/

open scoped BigOperators

namespace Module

variable {F A ι : Type*} [Field F] [IsAlgClosed F] [Ring A] [Algebra F A]
  [Fintype ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)]
  [∀ i, Module F (M i)] [∀ i, Module A (M i)] [∀ i, IsScalarTower F A (M i)]
  [∀ i, FiniteDimensional F (M i)] [∀ i, IsSimpleModule A (M i)]

private theorem end_component_scalar
    (hne : Pairwise fun i j => IsEmpty (M i ≃ₗ[A] M j))
    (T : Module.End A (Π i, M i)) (i : ι) :
    ∃ c : F, ∀ v : Π i, M i, (T v) i = c • v i := by
  classical
  let component (j : ι) : M j →ₗ[A] M i :=
    (LinearMap.proj i).comp (T.comp (LinearMap.single A M j))
  obtain ⟨c, hc⟩ :=
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed F).surjective (component i)
  refine ⟨c, fun v => ?_⟩
  have hzero (j : ι) (hj : j ≠ i) : component j = 0 := by
    by_contra hz
    exact (hne hj).false (LinearEquiv.ofBijective (component j)
      (LinearMap.bijective_of_ne_zero hz))
  calc
    (T v) i = ∑ j, component j (v j) := by
      conv_lhs => rw [← Finset.univ_sum_single v]
      simp only [map_sum, Finset.sum_apply]
      rfl
    _ = component i (v i) := by
      apply Finset.sum_eq_single i
      · intro j _ hj
        rw [hzero j hj, LinearMap.zero_apply]
      · simp
    _ = c • v i := by
      rw [← hc]
      rfl

public theorem exists_simultaneous_smul_eq
    (hne : Pairwise fun i j => IsEmpty (M i ≃ₗ[A] M j))
    (f : ∀ i, Module.End F (M i)) :
    ∃ a : A, ∀ i (v : M i), a • v = f i v := by
  classical
  let N := Π i, M i
  let f' : Module.End F N := LinearMap.pi fun i => (f i).comp (LinearMap.proj i)
  have hcomm (T : Module.End A N) (v : N) : f' (T v) = T (f' v) := by
    funext i
    obtain ⟨c, hc⟩ := end_component_scalar (F := F) M hne T i
    change f i ((T v) i) = (T (f' v)) i
    rw [hc, hc, map_smul]
    rfl
  let f'' : Module.End (Module.End A N) N :=
    { f'.toAddHom with
      map_smul' T v := hcomm T v }
  let b := Module.finBasis F N
  obtain ⟨a, ha⟩ := jacobson_density f'' (Finset.univ.image b)
  have heq : f' = (Module.toModuleEnd F (S := A) N) a := by
    apply b.ext
    intro j
    exact ha (b j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  refine ⟨a, fun i v => ?_⟩
  have h := congrArg (fun T : Module.End F N => T (Pi.single i v) i) heq
  change f i (Pi.single i v i) = a • Pi.single i v i at h
  simpa only [Pi.single_eq_same] using h.symm

end Module
