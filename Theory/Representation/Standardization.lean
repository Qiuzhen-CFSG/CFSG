module

public import Mathlib.Analysis.Complex.Basic
public import Theory.Representation.RepEquiv
public import Theory.Representation.Unbundled

/-!
# Standard coordinate models of complex representations

Transport a finite-dimensional complex representation along a basis to
`Fin (finrank ℂ V) → ℂ`. Conjugation preserves its character and irreducibility.

Extracted from the representation infrastructure for Peterfalvi (1.4),
`FeitThompson/PFsection1/PFsection1_4.lean`; historical names are preserved.
-/

noncomputable section
namespace Section1

@[expose] public noncomputable def standardizeRepresentation
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    Representation ℂ G (Fin (Module.finrank ℂ V) → ℂ) := by
  let b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V := Module.finBasis ℂ V
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := b.equivFun
  refine
    { toFun := fun g => e.conj (ρ g)
      map_one' := by
        ext x
        simp [LinearEquiv.conj_apply]
      map_mul' := by
        intro g h
        ext x
        simp [LinearEquiv.conj_apply, map_mul] }

public theorem standardizeRepresentation_character
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    (standardizeRepresentation ρ).character g = ρ.character g := by
  dsimp [standardizeRepresentation, Representation.character]
  exact LinearMap.trace_conj' (R := ℂ) (M := V)
    (N := Fin (Module.finrank ℂ V) → ℂ) (ρ g)
    (Module.Basis.equivFun (Module.finBasis ℂ V))

public theorem standardizeRepresentation_irreducible
    {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : Representation.IsIrreducible ρ) :
    Representation.IsIrreducible (standardizeRepresentation ρ) := by
  let b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V := Module.finBasis ℂ V
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := b.equivFun
  let eRep : Representation.RepEquiv ρ (standardizeRepresentation ρ) := by
    refine
      { toLinearEquiv := e
        isIntertwining' := ?_ }
    intro g
    ext v i
    have h := congrArg (fun w => w i)
      (LinearMap.toMatrix_mulVec_repr (v₁ := b) (v₂ := b) (f := ρ g) v)
    simp [standardizeRepresentation, e, b, b.equivFun_apply]
  exact (Representation.RepEquiv.irreducible_euqiv eRep).1 hρ

end Section1
