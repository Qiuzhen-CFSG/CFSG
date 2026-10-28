module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Interface
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.Generators
public import Theory.Representation.SubspaceQuotient
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Native M24 actions on certified subquotients

An injective map identifies an invariant image inside a genuine native action.
A surjective intertwiner then identifies a quotient of that image with the
prescribed matrices. Both invariance statements follow from the proved native
generator closure, rather than an abstract presentation or a coordinate slice.
`Certificate` packages left and right inverses and the four intertwining
identities; `Certificate.realization` constructs the resulting action.

The concrete degree-320 and degree-1242/1792 consumers are in
`NativeSubquotient.Models`. Their finite certificates remain explicit inputs.
The proof generalizes the native degree-220 quotient and degree-252 image
transports without changing those public interfaces.

Sources: James, The modular characters of the Mathieu groups, J. Algebra 27
(1973), 57–111; GM02 Proposition 5.1 and Aschbacher–Smith K.4, printed p.457.
-/

@[expose] public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient
open Sporadic.Mathieu Degree220Pair

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Restrict a genuine native action to an injectively parametrized invariant image.
Invariance is deduced from the two intertwining equations and native generation. -/
theorem of_embedding {d : ℕ} (σ : Representation (ZMod 2) M24 V)
    (A B : Matrix (Fin d) (Fin d) (ZMod 2))
    (E : (Fin d → ZMod 2) →ₗ[ZMod 2] V) (hE : Function.Injective E)
    (hA : (σ generatorA).comp E = E.comp (Matrix.toLin' A))
    (hB : (σ generatorB).comp E = E.comp (Matrix.toLin' B)) :
    ∃ ρ : Representation (ZMod 2) M24 (Fin d → ZMod 2),
      LinearMap.toMatrix' (ρ generatorA) = A ∧
      LinearMap.toMatrix' (ρ generatorB) = B := by
  have hinv (g : M24) : E.range ≤ E.range.comap (σ g) := by
    apply Submonoid.induction_of_closure_eq_top_left
      (motive := fun g => E.range ≤ E.range.comap (σ g))
      native_generators_monoid_closure g
    · intro v hv
      simpa only [map_one, Module.End.one_apply, Submodule.mem_comap] using hv
    · rintro _ (rfl | rfl) y ih v hv
      · obtain ⟨w, hw⟩ := ih hv
        refine ⟨Matrix.toLin' A w, ?_⟩
        change E (Matrix.toLin' A w) = σ (generatorA * y) v
        rw [map_mul, Module.End.mul_apply, ← hw]
        exact (congrArg (fun f => f w) hA).symm
      · obtain ⟨w, hw⟩ := ih hv
        refine ⟨Matrix.toLin' B w, ?_⟩
        change E (Matrix.toLin' B w) = σ (generatorB * y) v
        rw [map_mul, Module.End.mul_apply, ← hw]
        exact (congrArg (fun f => f w) hB).symm
  let e := LinearEquiv.ofInjective E hE
  let ρ : Representation (ZMod 2) M24 (Fin d → ZMod 2) :=
    e.symm.conjRingEquiv.toMonoidHom.comp (σ.subrepresentation E.range hinv)
  have he (g : M24) (v : Fin d → ZMod 2) : E (ρ g v) = σ g (E v) := by
    change E (e.symm ⟨σ g (E v), _⟩) = _
    rw [LinearEquiv.ofInjective_symm_apply]
  have hm (g : M24) (M : Matrix (Fin d) (Fin d) (ZMod 2))
      (h : (σ g).comp E = E.comp (Matrix.toLin' M)) :
      LinearMap.toMatrix' (ρ g) = M := by
    have hl : ρ g = Matrix.toLin' M := by
      apply LinearMap.ext
      intro v
      apply hE
      rw [he]
      exact congrArg (fun f => f v) h
    rw [hl, LinearMap.toMatrix'_toLin']
  exact ⟨ρ, hm generatorA A hA, hm generatorB B hB⟩

/-- Descend a genuine native action through the kernel of a surjective intertwiner.
The kernel's invariance is proved on the full native group. -/
theorem of_quotient {d : ℕ} (σ : Representation (ZMod 2) M24 V)
    (A B : Matrix (Fin d) (Fin d) (ZMod 2))
    (P : V →ₗ[ZMod 2] (Fin d → ZMod 2)) (hP : Function.Surjective P)
    (hA : P.comp (σ generatorA) = (Matrix.toLin' A).comp P)
    (hB : P.comp (σ generatorB) = (Matrix.toLin' B).comp P) :
    ∃ ρ : Representation (ZMod 2) M24 (Fin d → ZMod 2),
      LinearMap.toMatrix' (ρ generatorA) = A ∧
      LinearMap.toMatrix' (ρ generatorB) = B := by
  let K : Subrepresentation σ :=
    { toSubmodule := P.ker
      apply_mem_toSubmodule := by
        intro g
        apply Submonoid.induction_of_closure_eq_top_left
          (motive := fun g => ∀ v, v ∈ P.ker → σ g v ∈ P.ker)
          native_generators_monoid_closure g
        · intro v hv
          simpa only [map_one, Module.End.one_apply] using hv
        · rintro _ (rfl | rfl) y ih v hv
          · change P (σ (generatorA * y) v) = 0
            rw [map_mul, Module.End.mul_apply, ← LinearMap.comp_apply, hA,
              LinearMap.comp_apply, show P (σ y v) = 0 from ih v hv, map_zero]
          · change P (σ (generatorB * y) v) = 0
            rw [map_mul, Module.End.mul_apply, ← LinearMap.comp_apply, hB,
              LinearMap.comp_apply, show P (σ y v) = 0 from ih v hv, map_zero] }
  let e := P.quotKerEquivOfSurjective hP
  let ρ : Representation (ZMod 2) M24 (Fin d → ZMod 2) :=
    e.conjRingEquiv.toMonoidHom.comp K.quotientRepresentation
  have he (g : M24) (v : V) : ρ g (P v) = P (σ g v) := by
    change e (K.quotientRepresentation g (e.symm (P v))) = _
    dsimp only [e]
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    exact P.quotKerEquivOfSurjective_apply_mk hP (σ g v)
  have hm (g : M24) (M : Matrix (Fin d) (Fin d) (ZMod 2))
      (h : P.comp (σ g) = (Matrix.toLin' M).comp P) :
      LinearMap.toMatrix' (ρ g) = M := by
    have hl : ρ g = Matrix.toLin' M := by
      apply LinearMap.ext
      intro v
      obtain ⟨w, rfl⟩ := hP v
      rw [he]
      exact congrArg (fun f => f w) h
    rw [hl, LinearMap.toMatrix'_toLin']
  exact ⟨ρ, hm generatorA A hA, hm generatorB B hB⟩

/-- Two-stage native realization: first certify the source submodule, then its
quotient. No arbitrary coordinate slice is assumed to carry an action. -/
theorem of_subquotient {u d : ℕ} (σ : Representation (ZMod 2) M24 V)
    (U₀ U₁ : Matrix (Fin u) (Fin u) (ZMod 2))
    (A B : Matrix (Fin d) (Fin d) (ZMod 2))
    (E : (Fin u → ZMod 2) →ₗ[ZMod 2] V) (hE : Function.Injective E)
    (hEA : (σ generatorA).comp E = E.comp (Matrix.toLin' U₀))
    (hEB : (σ generatorB).comp E = E.comp (Matrix.toLin' U₁))
    (P : Matrix (Fin d) (Fin u) (ZMod 2))
    (hP : Function.Surjective (Matrix.toLin' P))
    (hPA : P * U₀ = A * P) (hPB : P * U₁ = B * P) :
    ∃ ρ : Representation (ZMod 2) M24 (Fin d → ZMod 2),
      LinearMap.toMatrix' (ρ generatorA) = A ∧
      LinearMap.toMatrix' (ρ generatorB) = B := by
  obtain ⟨τ, hτA, hτB⟩ := of_embedding σ U₀ U₁ E hE hEA hEB
  apply of_quotient τ A B (Matrix.toLin' P) hP
  · apply LinearMap.toMatrix'.injective
    simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', hτA]
    exact hPA
  · apply LinearMap.toMatrix'.injective
    simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', hτB]
    exact hPB

/-- The literal transpose convention of the two largest ATLAS models. -/
theorem nativeRealization_of_subquotient {u d : ℕ}
    (σ : Representation (ZMod 2) M24 V)
    (U₀ U₁ : Matrix (Fin u) (Fin u) (ZMod 2))
    (A B : Matrix (Fin d) (Fin d) (ZMod 2))
    (E : (Fin u → ZMod 2) →ₗ[ZMod 2] V) (hE : Function.Injective E)
    (hEA : (σ generatorA).comp E = E.comp (Matrix.toLin' U₀))
    (hEB : (σ generatorB).comp E = E.comp (Matrix.toLin' U₁))
    (P : Matrix (Fin d) (Fin u) (ZMod 2))
    (hP : Function.Surjective (Matrix.toLin' P))
    (hPA : P * U₀ = A.transpose * P) (hPB : P * U₁ = B.transpose * P) :
    Nonempty (Degrees12421792.NativeRealization A B) := by
  obtain ⟨ρ, hA, hB⟩ := of_subquotient σ U₀ U₁ A.transpose B.transpose E hE hEA hEB
    P hP hPA hPB
  exact ⟨⟨ρ, hA, hB⟩⟩


/-- Rectangular finite certificates for a quotient of an invariant source image.
The left and right inverse identities certify the two required rank conditions. -/
structure Certificate {u d : ℕ} (σ : Representation (ZMod 2) M24 V)
    (A B : Matrix (Fin d) (Fin d) (ZMod 2)) where
  sourceA : Matrix (Fin u) (Fin u) (ZMod 2)
  sourceB : Matrix (Fin u) (Fin u) (ZMod 2)
  embedding : (Fin u → ZMod 2) →ₗ[ZMod 2] V
  retraction : V →ₗ[ZMod 2] (Fin u → ZMod 2)
  embedding_leftInverse : retraction.comp embedding = LinearMap.id
  embedding_A : (σ generatorA).comp embedding = embedding.comp (Matrix.toLin' sourceA)
  embedding_B : (σ generatorB).comp embedding = embedding.comp (Matrix.toLin' sourceB)
  projection : Matrix (Fin d) (Fin u) (ZMod 2)
  sectionMatrix : Matrix (Fin u) (Fin d) (ZMod 2)
  projection_rightInverse : projection * sectionMatrix = 1
  projection_A : projection * sourceA = A * projection
  projection_B : projection * sourceB = B * projection

/-- A certificate constructs an action; it does not assume a native action on the
quotient coordinates or invariant source image. -/
theorem Certificate.realization {u d : ℕ} {σ : Representation (ZMod 2) M24 V}
    {A B : Matrix (Fin d) (Fin d) (ZMod 2)} (c : Certificate (u := u) σ A B) :
    ∃ ρ : Representation (ZMod 2) M24 (Fin d → ZMod 2),
      LinearMap.toMatrix' (ρ generatorA) = A ∧
      LinearMap.toMatrix' (ρ generatorB) = B := by
  have hE : Function.Injective c.embedding := by
    intro v w h
    have he (x : Fin u → ZMod 2) : c.retraction (c.embedding x) = x :=
      congrArg (fun f => f x) c.embedding_leftInverse
    exact (he v).symm.trans ((congrArg c.retraction h).trans (he w))
  have hP : Function.Surjective (Matrix.toLin' c.projection) := by
    intro v
    refine ⟨Matrix.toLin' c.sectionMatrix v, ?_⟩
    change (Matrix.toLin' c.projection ∘ₗ Matrix.toLin' c.sectionMatrix) v = v
    rw [← Matrix.toLin'_mul, c.projection_rightInverse, Matrix.toLin'_one]
    rfl
  exact of_subquotient σ c.sourceA c.sourceB A B c.embedding hE c.embedding_A
    c.embedding_B c.projection hP c.projection_A c.projection_B

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient

