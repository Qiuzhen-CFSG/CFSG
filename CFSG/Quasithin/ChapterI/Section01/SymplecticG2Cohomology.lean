module

public import Theory.Representation.SymplecticNatural
public import Theory.Representation.FirstCohomologyCyclic

/-!
# I.1.6(5): natural symplectic and G₂ cohomology

The symplectic action here is the actual matrix action of the derived group.
An intertwining identification transports its cocycles and principal cocycles;
the scalar-restriction theorem then converts the defining-field dimension to
the binary dimension. The field order, rather than a choice of finite-field
coordinates, determines the factor `n`.

This module currently supplies that reduction. The dimension-one calculations
over the defining field for `Sp₄(2^n)'` and the six-dimensional natural module
of `G₂(2^n)'` still require their family-specific cocycle normal forms.
In particular the latter is not the fourteen-dimensional adjoint module.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma I.1.6(5), printed p.408 (PDF p.419), citing Jones--Parshall (1976).
-/

namespace CFSG.Quasithin.ChapterI

open Representation Representation.OneCohomology

/-- An actual identification with the natural derived-symplectic module reduces
binary cohomology to the calculation over its defining field. This includes
`n = 1`, without replacing the derived group by the full symplectic group. -/
public theorem finrank_firstCohomology_of_symplecticDerived_natural
    {K G V : Type*} [Field K] [Finite K] [Algebra (ZMod 2) K]
    [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (n : ℕ) (hcard : Nat.card K = 2 ^ n)
    (eG : G ≃* commutator (Matrix.symplecticGroup (Fin 2) K))
    (eV : V ≃ₗ[ZMod 2] ((Fin 2 ⊕ Fin 2) → K))
    (he : ∀ g v, eV (ρ g v) = symplecticDerivedNatural 2 (eG g) (eV v)) :
    Module.finrank (ZMod 2) (H1 ρ) =
      n * Module.finrank K (H1 (symplecticDerivedNatural (k := K) 2)) := by
  let σ := restrictScalars (k := ZMod 2) (symplecticDerivedNatural (k := K) 2)
  have e : H1 ρ ≃ₗ[ZMod 2] H1 σ := H1Congr ρ σ eG eV he
  rw [e.finrank_eq, finrank_restrictScalars, coefficient_finrank_of_card 2 n hcard]

end CFSG.Quasithin.ChapterI
