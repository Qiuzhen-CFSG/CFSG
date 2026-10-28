module

public import Theory.Representation.EndFieldRep
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Traces Span the Schur Endomorphism Field

For a finite-dimensional irreducible representation over a finite field `F`,
the existing endomorphism-field representation has traces spanning its field
`E = End_{F[G]}(V)` as an `F`-vector space. The acting monoid need not be finite.
The statement uses the exact field and module structures of `EndFieldRep`.

Jacobson density makes the monoid algebra surject onto all `E`-linear
endomorphisms. Rank-one operators have arbitrary trace on the nonzero module.
The trace of an algebra element is an `F`-linear combination of the traces of
monoid elements, giving the claimed span.

This standard Schur-field argument supplies the trace-field input for
Frobenius-period descent of finite-field irreducible representations, used in
the dimension reduction following Fong--Wong (1.15), p. 149.
-/

open scoped MonoidAlgebra

namespace Representation

variable {F G V : Type*} [Field F] [Finite F] [Monoid G] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (ρ : Representation F G V) [ρ.IsIrreducible]

public theorem span_range_endFieldRep_trace : Submodule.span F (Set.range fun g =>
    LinearMap.trace (Module.End F[G] ρ.asModule) ρ.asModule (endFieldRep ρ g)) = ⊤ := by
  let E := Module.End F[G] ρ.asModule
  have : IsSimpleModule F[G] ρ.asModule := (irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  have hnontriv : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  have : Nontrivial ρ.asModule := ρ.asModuleEquiv.nontrivial
  have : Finite ρ.asModule := Module.finite_iff_finite.mp (inferInstance : Module.Finite F ρ.asModule)
  have : Module.Finite E ρ.asModule := Module.Finite.of_finite
  let W : Submodule F E := Submodule.span F (Set.range fun g => LinearMap.trace E ρ.asModule (endFieldRep ρ g))
  have htr (a : F[G]) : LinearMap.trace E ρ.asModule (Module.toModuleEnd E (S := F[G]) ρ.asModule a) ∈ W := by
    induction a using MonoidAlgebra.induction_linear with
    | zero =>
      have hz : Module.toModuleEnd E (S := F[G]) ρ.asModule 0 = 0 := by ext v; exact zero_smul _ _
      rw [hz, map_zero]
      exact W.zero_mem
    | add a b ha hb => simpa only [map_add] using W.add_mem ha hb
    | single g c =>
      have he : Module.toModuleEnd E (S := F[G]) ρ.asModule (MonoidAlgebra.single g c) =
          (algebraMap F E c) • endFieldRep ρ g := by
        ext v
        change MonoidAlgebra.single g c • v = (algebraMap F E c) • endFieldRep ρ g v
        rw [algebraMap_smul E c]
        apply ρ.asModuleEquiv.injective
        simp only [asModuleEquiv_map_smul, asAlgebraHom_single, LinearMap.smul_apply,
          endFieldRep_apply, LinearEquiv.map_smul, LinearEquiv.apply_symm_apply]
      rw [he, map_smul]
      exact W.smul_mem c (Submodule.subset_span ⟨g, rfl⟩)
  apply top_unique
  intro c _
  obtain ⟨v, hv⟩ := exists_ne (0 : ρ.asModule)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one E hv
  have hsurj : Function.Surjective (Module.toModuleEnd E (S := F[G]) ρ.asModule) :=
    Module.Finite.toModuleEnd_moduleEnd_surjective
  obtain ⟨a, ha⟩ := hsurj (f.smulRight (c • v))
  have h := htr a
  rw [ha, LinearMap.trace_smulRight, map_smul, hf, smul_eq_mul, mul_one] at h
  exact h

end Representation

