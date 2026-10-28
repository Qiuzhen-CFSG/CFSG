module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Data
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.Model

/-!
# Independent contracts for the concrete cubic calculation

The coordinate contract identifies the original induced module with the
126 coordinates, with two generating actors and their exact matrices.
It contains no invariant flag. The independent arithmetic contract asserts
square-zero, rank 21, and the two commutation identities for the fixed
matrix over every characteristic-two field. Neither contract is proved here.

Together these contracts supply a square-zero intertwiner on the literal
principal series. They separate the finite matrix certificate from the
unitary-group, Borel, character and induction convention comparisons.
Source motivation: Guralnick–Malle, Proposition 4.3, p.10.
-/

@[expose] public section
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag
universe v

/-- Coordinates for the original induced module. When using the retained
GAP right action, `actor` must account for group inversion, and `z` must
account for the inverse Borel character. -/
structure Coordinates {K : Type*} [Field K] [CharP K 2]
    (χ : standardBorel modelForm →* Kˣ) where
  z : K
  quadratic : z ^ 2 + z + 1 = 0
  equiv : IndV (standardBorel modelForm).subtype (scalarCharacter χ) ≃ₗ[K] (Fin 126 → K)
  actor : Fin 2 → standardGroup modelForm
  generates : Subgroup.closure (Set.range actor) = ⊤
  action : ∀ a v, equiv (ind (standardBorel modelForm).subtype (scalarCharacter χ) (actor a) v) =
    (generatorMatrix z quadratic a).mulVec (equiv v)

def ModelCoordinates : Prop :=
  ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
    (χ : standardBorel modelForm →* Kˣ),
    χ ≠ 1 → (∀ b, χ b ^ 3 = 1) → Nonempty (Coordinates χ)

/-- Concrete arithmetic about the defined matrix, without a representation
or an assumed invariant subspace. The arithmetic owner must prove all fields. -/
structure MatrixRelations : Prop where
  square_zero : ∀ (K : Type v) [Field K] [CharP K 2]
    (z : K) (hz : z ^ 2 + z + 1 = 0),
    nilpotentMatrix z hz * nilpotentMatrix z hz = 0
  rank : ∀ (K : Type v) [Field K] [CharP K 2]
    (z : K) (hz : z ^ 2 + z + 1 = 0),
    Module.finrank K (LinearMap.range (nilpotentMatrix z hz).toLin') = 21
  commutes : ∀ (K : Type v) [Field K] [CharP K 2]
    (z : K) (hz : z ^ 2 + z + 1 = 0) (a : Fin 2),
    nilpotentMatrix z hz * generatorMatrix z hz a =
      generatorMatrix z hz a * nilpotentMatrix z hz

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag
