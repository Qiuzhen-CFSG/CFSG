module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.CertificateData
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.GeneratorMatrices
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.FlagTools
public import Mathlib.RingTheory.SimpleModule.Rank

/-!
# Contracts and assembly for the eight actual adjoint factors

An invariant flag with coordinates on its literal successive quotients and
binary simplicity of the eight displayed matrix pairs suffice for the desired
filtration. These are separate finite calculations. Simplicity is stated as
absence of nonzero proper invariant binary subspaces, so it does not impose
absolute irreducibility or a full binary endomorphism algebra.

The witness record includes no simplicity premise. Its generator identities
refer to the native M22 generators and the exact diagonal matrices saved in
`CertificateData`. The theorem at the end applies the two inputs to the actual
352-dimensional representation. Both inputs remain to be constructed before
this becomes an unconditional theorem about the induced adjoint.

Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16;
Aschbacher--Smith, Chapter K, printed pp.451--452 and 457.
-/

@[expose] public section
open Representation Sporadic.Mathieu
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration

/-- Coordinates on the actual quotients of a native invariant flag. -/
structure FlagCoordinates where
  stage : ℕ → Subrepresentation GeneratorMatrices.binaryAdjoint
  zero : stage 0 = ⊥
  last : stage 8 = ⊤
  mono : ∀ m, m < 8 → stage m ≤ stage (m + 1)
  coordinates (t : Factor) :
    ((stage (t.val + 1)).toSubmodule ⧸
      (within (stage t.val) (stage (t.val + 1))).toSubmodule) ≃ₗ[ZMod 2]
      (Fin (degree t) → ZMod 2)
  generator_coordinates : ∀ (t : Factor) (k : Fin 2) v,
    coordinates t
      ((within (stage t.val) (stage (t.val + 1))).quotientRepresentation
        (GeneratorMatrices.generator k) v) =
      (factorMatrix t k).mulVec (coordinates t v)

/-- A finite binary matrix pair has no proper nonzero invariant subspace.
This does not assert absolute irreducibility. -/
def FactorSimple (t : Factor) : Prop :=
  ∀ W : Submodule (ZMod 2) (Fin (degree t) → ZMod 2),
    (∀ (k : Fin 2) v, v ∈ W → (factorMatrix t k).mulVec v ∈ W) →
    W = ⊥ ∨ W = ⊤

/-- A one-dimensional factor is simple independently of its generator matrices. -/
theorem factorSimple_of_degree_eq_one (t : Factor) (ht : degree t = 1) :
    FactorSimple t := by
  let : IsSimpleModule (ZMod 2) (Fin (degree t) → ZMod 2) :=
    isSimpleModule_iff_finrank_eq_one.mpr (by simp [ht])
  intro W _
  exact eq_bot_or_eq_top W

/-- The four one-dimensional entries of the saved flag need no further
matrix simplicity calculation. Their native quotient comparison is separate. -/
theorem small_factors_simple :
    FactorSimple 1 ∧ FactorSimple 3 ∧ FactorSimple 5 ∧ FactorSimple 6 := by
  exact ⟨factorSimple_of_degree_eq_one 1 rfl, factorSimple_of_degree_eq_one 3 rfl,
    factorSimple_of_degree_eq_one 5 rfl, factorSimple_of_degree_eq_one 6 rfl⟩

/-- Binary matrix simplicity passes to the representation with those coordinates. -/
theorem irreducible_of_factorSimple {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) M22 V) (t : Factor)
    (e : V ≃ₗ[ZMod 2] (Fin (degree t) → ZMod 2))
    (he : ∀ (k : Fin 2) v, e (ρ (GeneratorMatrices.generator k) v) =
      (factorMatrix t k).mulVec (e v))
    (hs : FactorSimple t) : IsIrreducible ρ := by
  let : NeZero (degree t) := ⟨Nat.ne_of_gt (degree_pos t)⟩
  let : Nontrivial V := e.toEquiv.nontrivial
  rw [IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let W := S.toSubmodule.map e.toLinearMap
  have hw : ∀ (k : Fin 2) v, v ∈ W → (factorMatrix t k).mulVec v ∈ W := by
    intro k v hv
    obtain ⟨x, hx, rfl⟩ := hv
    exact ⟨ρ (GeneratorMatrices.generator k) x, S.apply_mem_toSubmodule _ hx, he k x⟩
  rcases hs W hw with h | h
  · left
    apply le_antisymm _ bot_le
    intro v hv
    change v = 0
    apply e.injective
    have hv' : e v ∈ W := ⟨v, hv, rfl⟩
    rw [h] at hv'
    change e v = 0 at hv'
    exact hv'.trans (map_zero e).symm
  · right
    apply le_antisymm le_top
    intro v _
    have hv' : e v ∈ W := by rw [h]; trivial
    obtain ⟨w, hw, heq⟩ := hv'
    exact e.injective heq ▸ hw

/-- The literal invariant flag and the eight simplicity certificates produce
an actual factor-degree filtration, retaining all nonsplit extensions. -/
theorem binary_factorDegreeFiltration_of_certificates
    (C : FlagCoordinates) (hs : ∀ t : Factor, FactorSimple t) :
    FactorDegreeFiltration {d : ℕ | d ≤ 10 ∨ 30 < d} GeneratorMatrices.binaryAdjoint := by
  apply filtration_of_flag _ 8 C.stage C.zero C.last C.mono
  · intro m hm
    let t : Factor := ⟨m, hm⟩
    exact irreducible_of_factorSimple _ t (C.coordinates t) (C.generator_coordinates t) (hs t)
  · intro m hm
    let t : Factor := ⟨m, hm⟩
    have he := (C.coordinates t).finrank_eq
    rw [Module.finrank_fin_fun] at he
    change Module.finrank (ZMod 2)
      ((C.stage (t.val + 1)).toSubmodule ⧸
        (within (C.stage t.val) (C.stage (t.val + 1))).toSubmodule) ∈ _
    rw [he]
    exact degree_allowed t

end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration
