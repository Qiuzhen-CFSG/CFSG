module

public import Theory.Representation.FirstCohomologySymplecticFour.RootCocycle.QuadraticValues
public import Theory.Representation.FirstCohomologySymplecticFour.RootCocycle.LongRootValues
public import Theory.Representation.FirstCohomologySymplecticFour.RootCocycle.CrossRootValues

/-!
# Cocycle values on the eight standard symplectic root families

Over a finite field of characteristic two with more than two elements, every
cocycle of the natural symplectic four-space agrees with a scalar multiple of
the quadratic-defect cocycle plus a principal cocycle on all eight elementary
type-C₂ root families. The root matrices are defined in `Generation`.

First normalize the four long-root families using a single principal correction.
The explicit cross-root relations then identify the two scalar coefficients and
determine the remaining four families. This local calculation uses no generation
theorem; extending the equality to the whole group is a separate step.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma I.1.6(5), printed p.408 (local calculation towards the cohomology bound).
-/

public section

namespace Representation.OneCohomology.SymplecticFour

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

/-- Every cocycle on the natural symplectic four-space has one quadratic
coefficient and one principal correction valid on all eight standard root
families, over a finite characteristic-two field larger than the binary field. -/
theorem exists_root_normal_form (hcard : 2 < Nat.card K)
    (f : cocycles (symplecticNatural (k := K) 2)) :
    ∃ (t : K) (v : (Fin 2 ⊕ Fin 2) → K),
      ∀ (r : Fin 8) (u : K), f.val (rootElement r u) =
        (t • quadraticCocycle + principal (symplecticNatural 2) v).val (rootElement r u) := by
  obtain ⟨t0, t1, v, h0, h1, h2, h3⟩ := exists_longRoot_normal_form hcard f
  exact ⟨t0, v, (extend_longRoot_normal_form hcard f t0 t1 v h0 h1 h2 h3).2⟩

end Representation.OneCohomology.SymplecticFour
