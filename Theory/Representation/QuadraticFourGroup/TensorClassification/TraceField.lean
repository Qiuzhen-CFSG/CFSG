module

public import Theory.Representation.QuadraticFourGroup.TensorClassification.ExternalTensor
public import Theory.Representation.EndFieldTrace
public import Mathlib.Algebra.Algebra.ZMod

/-!
# The common field of a natural tensor

The traces of the Schur-field action span its coefficient field. If its
scalar extension is equivalent to a tensor of two Frobenius natural actions,
the tensor trace range is the embedded matrix field. Taking spans identifies
the two embedded fields and gives a compatible field isomorphism.

This proves the common-field step of GLS2 Theorem 25.14, Step 5, conditional
on the explicit equivalence over the extension field. Descent of that
representation equivalence is a separate argument.
-/

@[expose] public section

open scoped MonoidAlgebra TensorProduct
namespace Representation.QuadraticFourGroup.TensorClassification

private theorem range_eq_of_spanning_values {k E K F G : Type*}
    [Field k] [Field E] [Field K] [Field F]
    [Algebra k E] [Algebra k K] [Algebra k F]
    (ι : E →ₐ[k] F) (e : K →ₐ[k] F) (τ : G → E)
    (hspan : Submodule.span k (Set.range τ) = ⊤)
    (hvalues : Set.range (ι ∘ τ) = Set.range e) :
    Set.range ι = Set.range e := by
  apply Set.Subset.antisymm
  · rintro _ ⟨a, rfl⟩
    have hle : Submodule.span k (Set.range τ) ≤
        Submodule.comap ι.toLinearMap e.toLinearMap.range := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g, rfl⟩
      change ι (τ g) ∈ Set.range e
      rw [← hvalues]
      exact ⟨g, rfl⟩
    exact hle (hspan ▸ Submodule.mem_top)
  · rw [← hvalues]
    rintro _ ⟨g, rfl⟩
    exact ⟨τ g, rfl⟩

theorem exists_ringEquiv_of_range_eq {E K F : Type*}
    [Field E] [Field K] [Field F] (ι : E →+* F) (e : K →+* F)
    (hr : Set.range ι = Set.range e) :
    ∃ f : E ≃+* K, ∀ a, e (f a) = ι a := by
  classical
  have hex (a : E) : ∃ b : K, e b = ι a := by
    change ι a ∈ Set.range e
    rw [← hr]
    exact ⟨a, rfl⟩
  let f : E → K := fun a => (hex a).choose
  have hf (a : E) : e (f a) = ι a := (hex a).choose_spec
  let φ : E →+* K := {
    toFun := f
    map_one' := e.injective (by rw [hf, map_one, map_one])
    map_zero' := e.injective (by rw [hf, map_zero, map_zero])
    map_add' := fun a b => e.injective (by rw [hf, map_add, map_add, hf, hf])
    map_mul' := fun a b => e.injective (by rw [hf, map_mul, map_mul, hf, hf]) }
  have hsurj : Function.Surjective φ := by
    intro b
    obtain ⟨a, ha⟩ := hr.symm ▸ Set.mem_range_self (f := e) b
    exact ⟨a, e.injective ((hf a).trans ha)⟩
  exact ⟨RingEquiv.ofBijective φ ⟨φ.injective, hsurj⟩, hf⟩

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (σ : Representation (ZMod 2) (Factor n × Factor n) V) [σ.IsIrreducible]
  {F : Type*} [Field F] [Algebra (Module.End (ZMod 2)[Factor n × Factor n] σ.asModule) F]
  [Algebra (ZMod 2) F]
  [IsScalarTower (ZMod 2) (Module.End (ZMod 2)[Factor n × Factor n] σ.asModule) F]

theorem schurField_range_eq_of_equiv (e : GaloisField 2 n →+* F) (i j : ℕ)
    (φ : (extendScalars F σ.endFieldRep).Equiv
      (externalTensor (mappedFrobeniusNatural e i) (mappedFrobeniusNatural e j))) :
    Set.range (algebraMap (Module.End (ZMod 2)[Factor n × Factor n] σ.asModule) F) =
      Set.range e := by
  let E := Module.End (ZMod 2)[Factor n × Factor n] σ.asModule
  let : Finite σ.asModule := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) σ.asModule)
  let : Module.Finite E σ.asModule := Module.Finite.of_finite
  let ι : E →ₐ[ZMod 2] F := IsScalarTower.toAlgHom (ZMod 2) E F
  let e' : GaloisField 2 n →ₐ[ZMod 2] F := {
    __ := e
    commutes' := fun a => RingHom.congr_fun
      (Subsingleton.elim (e.comp (algebraMap (ZMod 2) (GaloisField 2 n)))
        (algebraMap (ZMod 2) F)) a }
  let τ : Factor n × Factor n → E := fun g => LinearMap.trace E σ.asModule (σ.endFieldRep g)
  apply range_eq_of_spanning_values ι e' τ (span_range_endFieldRep_trace σ)
  have hc : ι ∘ τ = (externalTensor (mappedFrobeniusNatural e i)
      (mappedFrobeniusNatural e j)).character := by
    funext g
    rw [← congrFun (Representation.char_iso φ) g]
    exact (LinearMap.trace_baseChange (σ.endFieldRep g) F).symm
  rw [hc]
  exact mappedFrobeniusTensor_character_range e i j

theorem exists_schurFieldEquiv_of_equiv (e : GaloisField 2 n →+* F) (i j : ℕ)
    (φ : (extendScalars F σ.endFieldRep).Equiv
      (externalTensor (mappedFrobeniusNatural e i) (mappedFrobeniusNatural e j))) :
    ∃ f : Module.End (ZMod 2)[Factor n × Factor n] σ.asModule ≃+* GaloisField 2 n,
      ∀ a, e (f a) = algebraMap _ F a :=
  exists_ringEquiv_of_range_eq _ e (schurField_range_eq_of_equiv σ e i j φ)

end Representation.QuadraticFourGroup.TensorClassification

end
