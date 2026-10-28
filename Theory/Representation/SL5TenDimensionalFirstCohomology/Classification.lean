module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Models
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.Seeds
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.ExteriorPresentation
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Classification of ten-dimensional irreducible binary SL₅(2) modules

A nonzero intertwiner from either exterior model to a ten-dimensional
irreducible module is surjective. Equality of dimensions then makes it an
isomorphism. Thus a nonzero vector satisfying the local relations from `Seeds`,
together with the universal presentation by these relations, suffices for the
exhaustive identification. Positive finrank supplies finite dimensionality.

`identification_of_finrank_ten` discharges both inputs using `SeedExtraction`
and `ExteriorPresentation`: every ten-dimensional irreducible binary SL₅(2)
module is equivalent to the exterior square or cube of the natural module.
The conditional reduction remains available separately. No absolute
irreducibility or splitting-field hypothesis is used.

This is the identification needed for Aschbacher--Smith, *The Classification of
Quasithin Groups*, Lemma I.1.6(7), printed p.408/PDF p.419. Cohomology calculations
and their final assembly belong to the parent module, which is not imported here.
-/

@[expose] public section

namespace Representation.SL5TenDimensional.Classification

/-- A nonzero map from either ten-dimensional model to an irreducible module
of dimension ten is an equivalence. Irreducibility of the source is not needed. -/
theorem equiv_of_nonzero_map
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Group V) [Representation.IsIrreducible (k := ZMod 2) ρ]
    (hdim : Module.finrank (ZMod 2) V = 10) (a : Fin 2)
    (f : (exteriorAction (degree a)).IntertwiningMap ρ) (hf : f ≠ 0) :
    Nonempty (ρ.Equiv (exteriorAction (degree a))) := by
  let : FiniteDimensional (ZMod 2) V := Module.finite_of_finrank_pos (by omega)
  have hs : Function.Surjective f := (IsIrreducible.surjective_or_eq_zero f).resolve_right hf
  have hi : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      ((finrank_model a).trans hdim.symm) (f := f.toLinearMap)).mpr hs
  exact ⟨(f.ofBijective ⟨hi, hs⟩).symm⟩

/-- Extracting a nonzero vector with the local relations and proving their
exterior-power presentation suffice for the exhaustive model identification.
Both inputs remain explicit here; this theorem alone is not the classification. -/
theorem identification_of_seed_and_presentation
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Group V) [Representation.IsIrreducible (k := ZMod 2) ρ]
    (hdim : Module.finrank (ZMod 2) V = 10)
    (hextract : ∃ a v, v ≠ 0 ∧ HasExteriorSeed ρ a v)
    (hpresent : ∀ a v, HasExteriorSeed ρ a v →
      ∃ f : (exteriorAction (degree a)).IntertwiningMap ρ, f (seed a) = v) :
    Nonempty (ρ.Equiv (exteriorAction 2)) ∨ Nonempty (ρ.Equiv (exteriorAction 3)) := by
  obtain ⟨a, v, hv, hlocal⟩ := hextract
  obtain ⟨f, hf⟩ := hpresent a v hlocal
  have hf0 : f ≠ 0 := by
    intro hzero
    apply hv
    simpa [hzero] using hf.symm
  have he := equiv_of_nonzero_map ρ hdim a f hf0
  fin_cases a
  · exact Or.inl he
  · exact Or.inr he

/-- Every ten-dimensional irreducible binary SL₅(2) representation is equivalent
to the exterior square or cube of the natural representation. Positive finrank
supplies finite dimensionality, and both local-relation inputs are discharged. -/
theorem identification_of_finrank_ten
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Group V) [Representation.IsIrreducible (k := ZMod 2) ρ]
    (hdim : Module.finrank (ZMod 2) V = 10) :
    Nonempty (ρ.Equiv (exteriorAction 2)) ∨ Nonempty (ρ.Equiv (exteriorAction 3)) := by
  exact identification_of_seed_and_presentation ρ hdim
    (exists_exteriorSeed_of_finrank_ten ρ hdim) (intertwiner_of_seed ρ)

end Representation.SL5TenDimensional.Classification
