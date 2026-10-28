module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.Models

/-!
# Native quotients need only a nonzero map when the target pair is dense

The image of an intertwiner is preserved by the target matrices. Density
makes it invariant under every matrix, so a nonzero vector and elementary
rank-one matrices fill the target. This removes numerical right inverses
from the native 1242 and 1792 constructions. The 1242 source still needs
an injective invariant embedding; no coordinate slice is treated as an action.

Source context: James, J. Algebra 27 (1973), 57–111; GM02 Proposition 5.1.
The literal transpose convention is retained in both concrete consumers.
-/

public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient
open Sporadic.Mathieu Degree220Pair MatrixDensity

private def preservingRange {d : ℕ} (W : Submodule (ZMod 2) (Fin d → ZMod 2)) :
    Subalgebra (ZMod 2) (Matrix (Fin d) (Fin d) (ZMod 2)) where
  carrier := {M | ∀ x ∈ W, M.mulVec x ∈ W}
  zero_mem' := by intro x _; simp
  one_mem' := by intro x hx; simpa using hx
  add_mem' := by
    intro M N hM hN x hx
    simpa only [Matrix.add_mulVec] using W.add_mem (hM x hx) (hN x hx)
  mul_mem' := by
    intro M N hM hN x hx
    simpa only [← Matrix.mulVec_mulVec] using hM _ (hN x hx)
  algebraMap_mem' := by
    intro r x hx
    simpa only [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
      using W.smul_mem r hx

/-- A nonzero quotient intertwiner onto a dense binary pair is surjective. -/
theorem surjective_of_dense_nonzero {d : ℕ} {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) M24 V)
    (A B : Matrix (Fin d) (Fin d) (ZMod 2)) (hd : DensePair A B)
    (P : V →ₗ[ZMod 2] (Fin d → ZMod 2)) (hP : P ≠ 0)
    (hA : P.comp (σ generatorA) = (Matrix.toLin' A).comp P)
    (hB : P.comp (σ generatorB) = (Matrix.toLin' B).comp P) :
    Function.Surjective P := by
  have hm (g : M24) (M : Matrix (Fin d) (Fin d) (ZMod 2))
      (he : P.comp (σ g) = (Matrix.toLin' M).comp P) : M ∈ preservingRange P.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨σ g x, congrArg (fun f => f x) he⟩
  have hfull : preservingRange P.range = ⊤ := hd _ (hm _ _ hA) (hm _ _ hB)
  obtain ⟨x, hx⟩ : ∃ x, P x ≠ 0 := by
    by_contra h
    push Not at h
    exact hP (LinearMap.ext h)
  obtain ⟨i, hi⟩ : ∃ i, P x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have hi1 : P x i = 1 := by
    have hb : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
    exact (hb (P x i)).resolve_left hi
  intro y
  have hy : Matrix.vecMulVec y (Pi.single i 1) ∈ preservingRange P.range := by
    rw [hfull]
    trivial
  have hz := hy (P x) ⟨x, rfl⟩
  simpa [Matrix.vecMulVec_mulVec, hi1] using hz

/-- Dense transposed ATLAS targets give a native realization from a nonzero
quotient intertwiner, without a separately certified right inverse. -/
theorem realization_of_dense_nonzero_quotient {d : ℕ} {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) M24 V)
    (A B : Matrix (Fin d) (Fin d) (ZMod 2)) (hd : DensePair A B)
    (P : V →ₗ[ZMod 2] (Fin d → ZMod 2)) (hP : P ≠ 0)
    (hA : P.comp (σ generatorA) = (Matrix.toLin' A.transpose).comp P)
    (hB : P.comp (σ generatorB) = (Matrix.toLin' B.transpose).comp P) :
    Nonempty (Degrees12421792.NativeRealization A B) := by
  obtain ⟨ρ, hρA, hρB⟩ := of_quotient σ A.transpose B.transpose P
    (surjective_of_dense_nonzero σ _ _ hd.transpose P hP hA hB) hA hB
  exact ⟨⟨ρ, hρA, hρB⟩⟩

/-- Literal degree-1792 consumer: only a nonzero map and its two generator
identities remain, with the target density supplied by the proved certificate. -/
theorem native1792_of_nonzero_quotient {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) M24 V)
    (P : V →ₗ[ZMod 2] (Fin 1792 → ZMod 2)) (hP : P ≠ 0)
    (hA : P.comp (σ generatorA) =
      (Matrix.toLin' Degrees12421792.Data1792.first.transpose).comp P)
    (hB : P.comp (σ generatorB) =
      (Matrix.toLin' Degrees12421792.Data1792.second.transpose).comp P) :
    Nonempty (Degrees12421792.NativeRealization
      Degrees12421792.Data1792.first Degrees12421792.Data1792.second) :=
  realization_of_dense_nonzero_quotient σ _ _ Degrees12421792.density1792 P hP hA hB

/-- Literal degree-1242 consumer: first certify the invariant source image,
then use density to prove surjectivity of its nonzero quotient map. -/
theorem native1242_of_nonzero_subquotient {u : ℕ} {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) M24 V)
    (U₀ U₁ : Matrix (Fin u) (Fin u) (ZMod 2))
    (E : (Fin u → ZMod 2) →ₗ[ZMod 2] V) (hE : Function.Injective E)
    (hEA : (σ generatorA).comp E = E.comp (Matrix.toLin' U₀))
    (hEB : (σ generatorB).comp E = E.comp (Matrix.toLin' U₁))
    (P : Matrix (Fin 1242) (Fin u) (ZMod 2)) (hP : Matrix.toLin' P ≠ 0)
    (hPA : P * U₀ = Degrees12421792.Data1242.first.transpose * P)
    (hPB : P * U₁ = Degrees12421792.Data1242.second.transpose * P) :
    Nonempty (Degrees12421792.NativeRealization
      Degrees12421792.Data1242.first Degrees12421792.Data1242.second) := by
  obtain ⟨τ, hτA, hτB⟩ := of_embedding σ U₀ U₁ E hE hEA hEB
  apply realization_of_dense_nonzero_quotient τ _ _ Degrees12421792.density1242
    (Matrix.toLin' P) hP
  · apply LinearMap.toMatrix'.injective
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', hτA] using hPA
  · apply LinearMap.toMatrix'.injective
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', hτB] using hPB

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient
