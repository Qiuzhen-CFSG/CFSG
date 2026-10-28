module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.Cosets
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.Data
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.FlagTools

/-!
# Assembly boundary for the M₁₁ eleven-coset certificates

An actual invariant flag supplies coordinates on its literal successive
quotients. Independently, common-invariant-subspace certificates for the
three nontrivial matrix pairs prove those quotients simple. Combining them
produces a factor-degree filtration, retaining all extension blocks and
using no semisimplicity assumption.

Both certificate premises remain explicit. `Data` and `Witness` alone do
not prove either one. The root degree-window theorem consumes the resulting
filtration, and its owner must supply both certificates in final assembly.
Source: James, J. Algebra 27 (1973), 57–111.
-/

@[expose] public section
open Sporadic.Mathieu
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees
open Data

noncomputable def generator (s : Fin 2) : M11 :=
  if s = 0 then m11GeneratorAInM11 else m11GeneratorBInM11

structure FlagCoordinates where
  stage : ℕ → Subrepresentation cosetRepresentation
  zero : stage 0 = ⊥
  last : stage 33 = ⊤
  mono : ∀ m, m < 33 → stage m ≤ stage (m + 1)
  coordinates : ∀ t : Factor,
    ((stage (t.val + 1)).toSubmodule ⧸
      (within (stage t.val) (stage (t.val + 1))).toSubmodule) ≃ₗ[ZMod 2]
      (Fin (degree t) → ZMod 2)
  generator_coordinates : ∀ (t : Factor) (s : Fin 2) v,
    coordinates t ((within (stage t.val) (stage (t.val + 1))).quotientRepresentation
      (generator s) v) = (factorMatrix t s).mulVec (coordinates t v)

private theorem irreducible_of_modelMatrices
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) M11 V) (i : Model)
    (e : V ≃ₗ[ZMod 2] (Fin (modelDegree i) → ZMod 2))
    (he : ∀ s v, e (ρ (generator s) v) = (modelMatrix i s).mulVec (e v))
    (h : SimpleMatrices) : ρ.IsIrreducible := by
  let : NeZero (modelDegree i) := ⟨Nat.ne_of_gt (modelDegree_pos i)⟩
  let : Nontrivial V := e.symm.injective.nontrivial
  refine ⟨?_⟩
  intro U
  have hstable : ∀ (s : Fin 2) (v : Fin (modelDegree i) → ZMod 2),
      v ∈ U.toSubmodule.map e.toLinearMap →
        (modelMatrix i s).mulVec v ∈ U.toSubmodule.map e.toLinearMap := by
    intro s v hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨ρ (generator s) w, U.apply_mem_toSubmodule _ hw, he s w⟩
  rcases h i _ hstable with hb | ht
  · left
    apply Subrepresentation.toSubmodule_injective
    change U.toSubmodule = ⊥
    simpa using hb
  · right
    apply Subrepresentation.toSubmodule_injective
    change U.toSubmodule = ⊤
    simpa using ht

theorem filtration_of_certificates (C : FlagCoordinates) (hsimple : SimpleMatrices) :
    FactorDegreeFiltration ({1, 10, 32, 44} : Set ℕ) cosetRepresentation := by
  apply filtration_of_flag ({1, 10, 32, 44} : Set ℕ) 33 C.stage C.zero C.last C.mono
  · intro m hm
    let t : Factor := ⟨m, hm⟩
    exact irreducible_of_modelMatrices _ (factorKind t) (C.coordinates t)
      (C.generator_coordinates t) hsimple
  · intro m hm
    let t : Factor := ⟨m, hm⟩
    have he := (C.coordinates t).finrank_eq
    rw [Module.finrank_fin_fun] at he
    change Module.finrank (ZMod 2)
      ((C.stage (t.val + 1)).toSubmodule ⧸
        (within (C.stage t.val) (C.stage (t.val + 1))).toSubmodule) ∈ _
    rw [he]
    exact degree_allowed t

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees
