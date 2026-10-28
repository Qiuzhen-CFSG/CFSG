module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.Restriction
public import Theory.AlgebraicGroup.Variety.AffineSpace

/-!
# Parameter space for the actual D4 root product

The parameter space is the given maximal torus times affine space with one
coordinate for each of the 24 realized roots. This uses the torus of the actual
ambient group and does not identify that group with a different D4 carrier.

Steinberg 6.2(b--c), `refs/KGroup/GLS3/Chapter2St2.tex`, suggests multiplying
negative-root coordinates, the torus coordinate and positive-root coordinates
to obtain a dense morphism from this space. This module defines the domain and
counts its root coordinates; existence or dominance of that morphism is not
asserted here.
-/

noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

omit [IsAlgClosed k] in
/-- The actual realized D4 root datum has 24 roots. -/
public theorem Geometry.root_card (S : Geometry K) : Nat.card S.roots.Root = 24 := by
  rw [Nat.card_congr S.rootIndex]
  have hsign : Nat.card ({-1, 1} : Set ℝ) = 2 := by
    norm_num [Set.ncard_insert_of_notMem]
  have hpairs : Nat.card {p : Fin 4 × Fin 4 // p.1 < p.2} = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [Nat.card_prod, Nat.card_prod, hsign, hpairs]

/-- The given torus and one affine coordinate for every actual root.
No multiplication parametrization or density statement is part of this definition. -/
@[expose] public def Geometry.rootProductParameterSpace (S : Geometry K) : Variety k := by
  let : Finite S.roots.Root := Finite.of_equiv _ S.rootIndex.symm
  exact Variety.prod S.torus.carrierVariety (affineSpaceVariety k S.roots.Root)

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
