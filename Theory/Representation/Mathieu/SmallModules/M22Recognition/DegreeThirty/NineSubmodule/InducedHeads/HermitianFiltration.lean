module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.Coordinates
public import Theory.Representation.FactorDegreeFiltration
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.Flag
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.NativeComparison
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration.FactorAlgebras

/-!
# Certificate assembly for the Hermitian nine-space induction

The checked native generator comparison identifies the actual Hermitian
induction with saved orientation zero. Its adapted basis retains all extension
blocks and gives a literal invariant flag, with successive quotient dimensions
98, 10, 1, 10, 34, 10, 1, 34. Checked full matrix algebras on these quotients
prove irreducibility without a splitting assumption.

`filtration` assembles the coordinate comparison and algebra certificates with
no remaining premises. The action is the 198-dimensional right-coset model of
`Models.induced false`, intertwined by `inducedCoordinateEquiv false`. The two
conditional assembly interfaces remain available for reuse.

Source: Guralnick--Malle I, Proposition 5.1, pp.15--16, used by
Aschbacher--Smith Chapter K, printed pp.451--452,457.
-/

@[expose] public noncomputable section
open Representation
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration

/-- An actual invariant flag and full quotient matrix algebras prove the
filtration, without a semisimplicity or splitting assumption. -/
theorem filtration_of_flag_matrices (i : Fin 2) (C : FlagCoordinates i)
    (hspan : ∀ (t : Factor)
      (Q : Subalgebra (ZMod 2) (Matrix (Fin (degree i t)) (Fin (degree i t)) (ZMod 2))),
      (∀ j, factorMatrix i t j ∈ Q) → Q = ⊤) :
    FactorDegreeFiltration ({1, 10, 34, 98} : Set ℕ) (coordinateAction false) := by
  apply filtration_of_flag ({1, 10, 34, 98} : Set ℕ) 8 C.stage C.zero C.last C.mono
  · intro m hm
    let t : Factor := ⟨m, hm⟩
    exact irreducible_of_coordinate_matrices (degree_pos i t) actor
      (factorMatrix i t) (C.coordinates t) (C.generator_coordinates t) (hspan t)
  · intro m hm
    let t : Factor := ⟨m, hm⟩
    have he := (C.coordinates t).finrank_eq
    rw [Module.finrank_fin_fun] at he
    change Module.finrank (ZMod 2)
      ((C.stage (t.val + 1)).toSubmodule ⧸
        (within (C.stage t.val) (C.stage (t.val + 1))).toSubmodule) ∈
      ({1, 10, 34, 98} : Set ℕ)
    rw [he]
    exact degree_allowed i t

/-- The concrete consumer of the model-comparison and density certificates.
The index labels a saved GAP orientation, not a Boolean label of the point module. -/
theorem filtration_of_generator_coordinates (i : Fin 2)
    (e : CoordinateSpace false ≃ₗ[ZMod 2] Space)
    (he : ∀ j v, e (coordinateAction false (actor j) v) =
      (generatorMatrix i j).mulVec (e v))
    (hspan : ∀ (t : Factor)
      (Q : Subalgebra (ZMod 2) (Matrix (Fin (degree i t)) (Fin (degree i t)) (ZMod 2))),
      (∀ j, factorMatrix i t j ∈ Q) → Q = ⊤) :
    FactorDegreeFiltration ({1, 10, 34, 98} : Set ℕ) (coordinateAction false) :=
  filtration_of_flag_matrices i (flagOfGeneratorCoordinates i e he) hspan

/-- The actual induction of the Hermitian nine-space has an invariant
filtration with irreducible factors of degrees 1, 10, 34 and 98. -/
theorem filtration :
    FactorDegreeFiltration ({1, 10, 34, 98} : Set ℕ) (coordinateAction false) := by
  obtain ⟨i, e, he⟩ := exists_generator_coordinates
  exact filtration_of_generator_coordinates i e he (fullFactorAlgebra i)

end Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration
