module

public import Theory.Representation.SpecialLinearNatural
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.ZMod.Basic

/-!
# The full Hom space forced by binary special-linear invariance

A subspace of Hom(F₂ⁿ,D), invariant under precomposition by SLₙ(2), contains
all maps into the span of its evaluations, for n at least two. A transvection
difference isolates a column value; a second transvection moves that value
back to its original column. Spanning the values and summing the columns
then gives the full space. No semisimplicity or finite-dimensional target
hypothesis is used.

The private coordinate calculation extends the checked three-dimensional
argument in Theory/Representation/BinaryThreeHomSaturation.lean to the
natural dimensions needed by the canonical quintic perfect-lift action.
-/

public section
namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl
open Representation
variable {D : Type*} [AddCommGroup D] [Module (ZMod 2) D] {n : ℕ}

private def shear_column (j : Fin n) :
    D →ₗ[ZMod 2] ((Fin n → ZMod 2) →ₗ[ZMod 2] D) where
  toFun d := (LinearMap.proj j).smulRight d
  map_add' d e := by ext v; simp [smul_add]
  map_smul' a d := by ext v; simp [smul_smul, mul_comm]

private theorem shear_column_apply (j : Fin n) (d : D) (v : Fin n → ZMod 2) :
    shear_column j d v = v j • d := rfl

private theorem shear_column_isolate
    (f : (Fin n → ZMod 2) →ₗ[ZMod 2] D) {i j : Fin n} (hij : i ≠ j) :
    f.comp (specialLinearNatural n (Matrix.SpecialLinearGroup.transvection hij 1)) - f =
      shear_column j (f (Pi.single i 1)) := by
  apply LinearMap.ext
  intro v
  change f (((1 : Matrix (Fin n) (Fin n) (ZMod 2)) + Matrix.single i j 1).mulVec v) - f v = _
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq, one_mul, map_add]
  rw [map_smul, add_sub_cancel_left, shear_column_apply]

/-- Invariance under the literal binary special-linear action forces every
linear map into the actual evaluation span, in every dimension at least two. -/
theorem precomposition_invariant_shears_eq_full_range
    (n : ℕ) (hn : 2 ≤ n)
    (S : Submodule (ZMod 2) ((Fin n → ZMod 2) →ₗ[ZMod 2] D))
    (hstable : ∀ g : Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
      ∀ f ∈ S, f.comp (specialLinearNatural n g) ∈ S) :
    let D₀ := Submodule.span (ZMod 2)
      {y : D | ∃ f ∈ S, ∃ w : Fin n → ZMod 2, f w = y}
    ∀ f : (Fin n → ZMod 2) →ₗ[ZMod 2] D,
      f ∈ S ↔ LinearMap.range f ≤ D₀ := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  let D₀ := Submodule.span (ZMod 2)
    {y : D | ∃ f ∈ S, ∃ w : Fin n → ZMod 2, f w = y}
  change ∀ f : (Fin n → ZMod 2) →ₗ[ZMod 2] D, f ∈ S ↔ LinearMap.range f ≤ D₀
  have hoff (f : (Fin n → ZMod 2) →ₗ[ZMod 2] D) (hf : f ∈ S)
      (i j : Fin n) (hij : i ≠ j) : shear_column j (f (Pi.single i 1)) ∈ S := by
    rw [←shear_column_isolate f hij]
    exact S.sub_mem (hstable _ f hf) hf
  have hcolumn (f : (Fin n → ZMod 2) →ₗ[ZMod 2] D) (hf : f ∈ S)
      (i j : Fin n) : shear_column j (f (Pi.single i 1)) ∈ S := by
    by_cases hij : i = j
    · subst j
      obtain ⟨k,hki⟩ := exists_ne i
      have hh := hoff (shear_column k (f (Pi.single i 1)))
        (hoff f hf i k hki.symm) k i hki
      simpa only [shear_column_apply, Pi.single_eq_same, one_smul] using hh
    · exact hoff f hf i j hij
  have hev (f : (Fin n → ZMod 2) →ₗ[ZMod 2] D) (hf : f ∈ S)
      (v : Fin n → ZMod 2) (j : Fin n) : shear_column j (f v) ∈ S := by
    have he : v = ∑ i : Fin n, v i • (Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) := by
      ext i
      simp [Pi.single_apply]
    rw [he, map_sum, map_sum]
    apply S.sum_mem
    intro i _
    rw [map_smul, map_smul]
    exact S.smul_mem (v i) (hcolumn f hf i j)
  have hall (j : Fin n) (y : D) (hy : y ∈ D₀) : shear_column j y ∈ S := by
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨f,hf,w,rfl⟩ := hy; exact hev f hf w j
    | zero => simp
    | add y z hy hz hi hj => simpa only [map_add] using S.add_mem hi hj
    | smul a y hy hi => simpa only [map_smul] using S.smul_mem a hi
  intro f
  constructor
  · intro hf y hy
    obtain ⟨w,rfl⟩ := hy
    exact Submodule.subset_span ⟨f,hf,w,rfl⟩
  · intro hf
    have he : f = ∑ j : Fin n, shear_column j (f (Pi.single j 1)) := by
      apply LinearMap.ext
      intro v
      simp only [LinearMap.sum_apply, shear_column_apply]
      simp_rw [←map_smul]
      rw [←map_sum]
      congr 1
      ext j
      simp [Pi.single_apply]
    rw [he]
    exact S.sum_mem (fun j _ => hall j _ (hf ⟨Pi.single j 1,rfl⟩))

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl
