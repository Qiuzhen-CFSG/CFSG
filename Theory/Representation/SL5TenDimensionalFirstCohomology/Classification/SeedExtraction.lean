module

public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.Seeds
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.LocalData
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.HighestVector
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Support
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification.SeedExtraction.Parabolic
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Assembly of the binary SL₅ highest-vector route to seed extraction

Three inputs suffice: a nonzero vector with local highest-vector relations,
the restriction of its support to a single middle root in dimension ten, and
generation of the exterior seed stabilizer by the indicated parabolic
generators. `LocalData` proves that these give the exact `HasExteriorSeed`
contract, without using model identification or absolute irreducibility.

`exists_exteriorSeed_of_finrank_ten` discharges all three inputs. The zero-Hecke
operators supply a nonzero local highest vector; dimension bounds force its
support to be a singleton middle root; and parabolic generation turns fixedness
under the local generators into fixedness under the entire exterior-seed
stabilizer. Thus extraction applies to every ten-dimensional irreducible binary
SL₅ module. The conditional assembly lemma remains available separately.

Source application: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma I.1.6(7), printed p.408/PDF p.419.
-/

@[expose] public section

namespace Representation.SL5TenDimensional.Classification

/-- Assemble the local highest-vector route. Each mathematical input is an
explicit hypothesis; this is not the unconditional seed-extraction theorem. -/
theorem exists_exteriorSeed_of_local_inputs
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Group V)
    (hhighest : ∃ (J : Finset (Fin 4)) (v : V), v ≠ 0 ∧ LocalHighestVector ρ J v)
    (hsupport : ∀ (J : Finset (Fin 4)) (v : V), v ≠ 0 → LocalHighestVector ρ J v →
      ∃ a : Fin 2, J = {boundaryRoot a})
    (hgen : ∀ (a : Fin 2) (g : Group), exteriorAction (degree a) g (seed a) = seed a →
      g ∈ Subgroup.closure (seedParabolicGenerators a)) :
    ∃ (a : Fin 2) (v : V), v ≠ 0 ∧ HasExteriorSeed ρ a v := by
  obtain ⟨J, v, hv, hlocal⟩ := hhighest
  obtain ⟨a, rfl⟩ := hsupport J v hv hlocal
  exact ⟨a, v, hv, hlocal.hasExteriorSeed (hgen a)⟩

/-- Every ten-dimensional irreducible binary SL₅ module contains a nonzero
vector with the stabilizer and three-term relations of an exterior square or
cube seed. No model identification or absolute irreducibility is assumed. -/
theorem exists_exteriorSeed_of_finrank_ten
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) Group V) [IsIrreducible ρ]
    (hdim : Module.finrank (ZMod 2) V = 10) :
    ∃ (a : Fin 2) (v : V), v ≠ 0 ∧ HasExteriorSeed ρ a v := by
  exact exists_exteriorSeed_of_local_inputs ρ
    (exists_localHighestVector_of_finrank_ten ρ hdim)
    (fun _ _ hv hlocal => hlocal.support_eq_boundaryRoot_of_finrank_ten hv hdim)
    mem_seedParabolicClosure_of_fixes_seed

end Representation.SL5TenDimensional.Classification
