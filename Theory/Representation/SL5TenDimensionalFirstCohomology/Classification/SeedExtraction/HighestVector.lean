module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.LocalData
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.HeckeAction
public import Theory.Representation.ZeroHecke.TypeA4Eigenvector
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Local highest vectors in ten-dimensional binary SL₅ modules

The upper-unitriangular fixed subspace is nonzero by the fixed-vector theorem
for finite 2-groups. Its four simple-root operators satisfy the type-A₄
zero-Hecke relations, so they have a common nonzero vector that each operator
fixes or kills. The roots fixing this vector form its support; the rank-one
identities translate these eigenvalues into the local highest-vector relations.

This proves the existence input for the seed-extraction route to
Aschbacher--Smith, *The Classification of Quasithin Groups*, Lemma I.1.6(7),
printed p.408/PDF p.419. No identification with an exterior model or absolute
irreducibility is used.
-/

public section

namespace Representation.SL5TenDimensional.Classification

open HeckeAction

/-- Every ten-dimensional irreducible binary SL₅ module has a nonzero vector
fixed by all upper transvections and satisfying all four rank-one alternatives. -/
theorem exists_localHighestVector_of_finrank_ten
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Group V) [IsIrreducible ρ]
    (hdim : Module.finrank (ZMod 2) V = 10) :
    ∃ (J : Finset (Fin 4)) (v : V), v ≠ 0 ∧ LocalHighestVector ρ J v := by
  classical
  have hpos : 0 < Module.finrank (ZMod 2) V := by omega
  let : FiniteDimensional (ZMod 2) V := Module.finite_of_finrank_pos hpos
  let : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
  let : Nontrivial (upperFixedSubmodule ρ) := upperFixedSubmodule_nontrivial ρ
  have hrelations : ZeroHecke.TypeA4Relations (restrictedOperator ρ) :=
    ⟨restrictedOperator_sq ρ,
      fun i j hij => (restrictedOperator_commute ρ i j (Or.inl hij)).eq,
      restrictedOperator_braid ρ⟩
  obtain ⟨v, hv, heigen⟩ :=
    ZeroHecke.exists_common_zero_or_fixed (restrictedOperator ρ) hrelations
  let J : Finset (Fin 4) := Finset.univ.filter (fun i => restrictedOperator ρ i v = v)
  refine ⟨J, (v : V), fun h => hv (Subtype.ext h), v.property, ?_, ?_⟩
  · intro i hi
    have hnot : restrictedOperator ρ i v ≠ v := by simpa [J] using hi
    exact (restrictedOperator_eq_zero_iff ρ i v).mp ((heigen i).resolve_left hnot)
  · intro i hi
    exact (restrictedOperator_eq_self_iff ρ i v).mp ((Finset.mem_filter.mp hi).2)

end Representation.SL5TenDimensional.Classification
