module

public import Theory.Representation.QuadraticFourGroup.TensorClassification.ScalarComparison
public import Theory.Representation.QuadraticFourGroup.TensorClassification.SchurReduction
public import Theory.Representation.QuadraticFourGroup.TensorClassification.TraceField
public import Theory.Representation.ScalarDescent

/-!
# Descent of a natural tensor from the Schur closure

Assume an actual equivalence from the Schur-field scalar extension of a binary
irreducible module to two Frobenius natural factors over its algebraic closure.
The traces identify the Schur field with the defining field. Transporting both
factor matrices through that identification yields a tensor over the Schur
field with the same scalar extension. Noether--Deuring descends the equivalence;
restriction to the binary field and the explicit tensor field comparison give
the precise `IsNaturalTensorAlong` conclusion.

This completes finite-field descent and common-field identification for GLS2,
Theorem 25.14, Step 5 and its remarks (ChapterG.tex, lines 786--788, 906--928).
The existence of the natural tensor over the algebraic closure remains a
separate premise; this module does not assert that classification.
-/

public noncomputable section

open scoped MonoidAlgebra TensorProduct
namespace Representation.QuadraticFourGroup.TensorClassification

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (σ : Representation (ZMod 2) (Factor n × Factor n) V) [σ.IsIrreducible]

/-- Descend a genuine natural tensor over the Schur closure to the published binary model. -/
theorem isNaturalTensorAlong_of_schurClosure_equiv
    (e : GaloisField 2 n →+* SchurClosure σ) (i j : ℕ)
    (φ : (schurClosureRep σ).Equiv
      (externalTensor (mappedFrobeniusNatural e i) (mappedFrobeniusNatural e j))) :
    IsNaturalTensorAlong (MonoidHom.id (Factor n × Factor n)) σ := by
  let E := SchurField σ
  let F := SchurClosure σ
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨f, hf⟩ := exists_schurFieldEquiv_of_equiv σ e i j φ
  let t₁ := (iterateFrobeniusEquiv (GaloisField 2 n) 2 i).toRingHom
  let t₂ := (iterateFrobeniusEquiv (GaloisField 2 n) 2 j).toRingHom
  let e₁ := f.symm.toRingHom.comp t₁
  let e₂ := f.symm.toRingHom.comp t₂
  let τ := externalTensor (naturalAction e₁) (naturalAction e₂)
  have hc₁ : (algebraMap E F).comp e₁ = e.comp t₁ := by
    ext a
    symm
    simpa [e₁] using hf (f.symm (t₁ a))
  have hc₂ : (algebraMap E F).comp e₂ = e.comp t₂ := by
    ext a
    symm
    simpa [e₂] using hf (f.symm (t₂ a))
  have q : (extendScalars F τ).Equiv
      (externalTensor (mappedFrobeniusNatural e i) (mappedFrobeniusNatural e j)) := by
    have q := naturalTensorBaseChange (F := F) e₁ e₂
    rw [hc₁, hc₂] at q
    exact q
  obtain ⟨d⟩ := repEquiv_of_extendScalars σ.endFieldRep τ
    ⟨RepEquiv.ofRepresentationEquiv (φ.trans q.symm)⟩
  let a : V ≃+ ((Fin 2 → E) ⊗[E] (Fin 2 → E)) :=
    σ.asModuleEquiv.symm.toAddEquiv.trans d.toLinearEquiv.toAddEquiv
  let b : V ≃ₗ[ZMod 2] ((Fin 2 → E) ⊗[E] (Fin 2 → E)) :=
    LinearEquiv.ofBijective (a.toAddMonoidHom.toZModLinearMap 2) a.bijective
  have hb : σ.Equiv (restrictScalars (k := ZMod 2) τ) := by
    refine Representation.Equiv.mk b (fun g => ?_)
    apply LinearMap.ext
    intro v
    exact d.isIntertwining g (σ.asModuleEquiv.symm v)
  have hf₁ : f.toRingHom.comp e₁ = t₁ := by ext a; exact f.apply_symm_apply _
  have hf₂ : f.toRingHom.comp e₂ = t₂ := by ext a; exact f.apply_symm_apply _
  have c := naturalTensorFieldEquiv f e₁ e₂
  rw [hf₁, hf₂] at c
  refine ⟨frobeniusNatural n i, frobeniusNatural n j,
    frobeniusNatural_injective n i, frobeniusNatural_injective n j, ⟨?_⟩⟩
  exact hb.trans c

end Representation.QuadraticFourGroup.TensorClassification
