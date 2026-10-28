module

public import Theory.SpecificGroups.AlternatingFiveTriangle
public import Theory.SpecificGroups.SL2.PrimeIcosahedral
public import BenderSuzuki.MatrixGroups.PSL2

/-!
# An alternating-five subgroup in prime-field `PSL₂`

For a prime `p > 5` with `p ≡ ±1 (mod 5)`, the icosahedral matrix
construction supplies a nontrivial projective `(2,3,5)` pair.  The abstract
triangle-presentation theorem then turns this pair into an injective copy of
`A₅` in `PSL₂(ZMod p)`.
-/

namespace Glauberman

open BenderSuzuki.MatrixGroups

/-- The Dickson icosahedral subgroup exists in the two permitted prime-field
residue classes. -/
public theorem exists_alternatingGroupFive_embedding_psl2_prime (p : ℕ)
    [Fact p.Prime] (hp : 5 < p) (hmod : p % 5 = 1 ∨ p % 5 = 4) :
    ∃ f : alternatingGroup (Fin 5) →* PSL2MatrixGroup (ZMod p),
      Function.Injective f := by
  obtain ⟨X, Y, hX, hX2, hY3, hXY5⟩ :=
    Matrix.SpecialLinearGroup.Icosahedral.exists_projective_generators_prime p hp hmod
  exact alternatingGroup.exists_injective_hom_of_triangle X Y hX hX2 hY3 hXY5

end Glauberman

namespace Glauberman.Dickson

open BenderSuzuki.MatrixGroups

/-- Namespace-specific alias for the Dickson classification development. -/
public theorem exists_alternatingGroupFive_embedding_psl2_prime (p : ℕ)
    [Fact p.Prime] (hp : 5 < p) (hmod : p % 5 = 1 ∨ p % 5 = 4) :
    ∃ f : alternatingGroup (Fin 5) →* PSL2MatrixGroup (ZMod p),
      Function.Injective f :=
  Glauberman.exists_alternatingGroupFive_embedding_psl2_prime p hp hmod

end Glauberman.Dickson
