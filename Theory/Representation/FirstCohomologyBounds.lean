module

public import Theory.GroupTheory.PPerfectHom
public import Theory.Representation.FirstCohomology

/-!
# Bounds from first cohomology

The connecting map for a trivial quotient is injective modulo the original
module when the ambient representation has no fixed points.  This file records
the resulting finite-dimensional bound and a reusable p-perfect criterion for
that fixed-point condition.

Reference: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
C.1.13, printed pp.124--125.
-/

@[expose] public section

namespace Representation.OneCohomology

variable {k A W : Type*} [Field k] [Group A]
  [AddCommGroup W] [Module k W]

/-- A p-perfect group has no detected fixed vectors when their displacement
maps inject into a p-group. -/
public theorem fixed_eq_bot_of_pPerfect_detection
    {p : ℕ} {P : Type*} [Fact p.Prime] [Group P]
    (ρ : Representation k A W) (hA : IsPPerfect p A) (hP : IsPGroup p P)
    (displacement : fixed ρ → A →* P)
    (hdisplacement : Function.Injective displacement) : fixed ρ = ⊥ := by
  apply bot_unique
  intro w hw
  let w' : fixed ρ := ⟨w, hw⟩
  have hone (x : fixed ρ) : displacement x = 1 :=
    hA.hom_eq_one_of_isPGroup hP (displacement x)
  have hwzero : w' = 0 := hdisplacement (by rw [hone w', hone 0])
  exact congrArg Subtype.val hwzero

/-- Transport the connecting map through a concrete linear model of its
domain. -/
public def linearEquivToH1
    (ρ : Representation k A W) (V : Subrepresentation ρ)
    (h : HasTrivialQuotient V) {X : Type*} [AddCommGroup X] [Module k X]
    (e : X ≃ₗ[k] (W ⧸ V.toSubmodule)) : X →ₗ[k] H1 V.toRepresentation :=
  (quotientToH1 V h).comp e.toLinearMap

/-- The transported connecting map is injective when the ambient module is
fixed-point-free. -/
public theorem linearEquivToH1_injective
    (ρ : Representation k A W) (V : Subrepresentation ρ)
    (h : HasTrivialQuotient V) (hfixed : fixed ρ = ⊥)
    {X : Type*} [AddCommGroup X] [Module k X]
    (e : X ≃ₗ[k] (W ⧸ V.toSubmodule)) :
    Function.Injective (linearEquivToH1 ρ V h e) := by
  exact (quotientToH1_injective V h hfixed).comp e.injective

/-- The finite-dimensional consequence of the transported connecting map. -/
public theorem finrank_le_H1_of_linearEquiv
    [Finite A] [FiniteDimensional k W]
    (ρ : Representation k A W) (V : Subrepresentation ρ)
    (h : HasTrivialQuotient V) (hfixed : fixed ρ = ⊥)
    {X : Type*} [AddCommGroup X] [Module k X]
    (e : X ≃ₗ[k] (W ⧸ V.toSubmodule)) :
    Module.finrank k X ≤ Module.finrank k (H1 V.toRepresentation) := by
  exact LinearMap.finrank_le_finrank_of_injective
    (linearEquivToH1_injective ρ V h hfixed e)

end Representation.OneCohomology
