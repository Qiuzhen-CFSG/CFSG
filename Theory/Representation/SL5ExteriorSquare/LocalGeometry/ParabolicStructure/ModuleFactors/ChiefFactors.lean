module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.Stabilizers
public import Theory.Representation.SubspaceQuotient
public import Theory.Representation.SubrepresentationLattice
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Actual chief factors of the first exterior parabolic

This module records the literal restricted and quotient representations attached
 to the invariant chain `0 < V₁ < V₇ < V`.  The representations are built from
 the actual exterior-square action of `SL₅(F₂)` and the actual parabolic
 stabilizer; no family tag or abstract ten-dimensional carrier is used.

The one-dimensional first factor is proved irreducible here.  The middle and
last factors retain their quotient representations explicitly; their model
intertwiners and irreducibility certificates are separate declarations so that
those calculations cannot be hidden in a dimension or invariance argument.

Source: Aschbacher--Smith, Lemma 12.5.2(1), printed p.817/PDF p.834.
-/

@[expose] public section

namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

noncomputable section

/-- The literal exterior-square action restricted to the actual two-space
parabolic. -/
def firstParabolicRepresentation :
    Representation (ZMod 2) (parabolic 2) V :=
  (exteriorAction 2).comp (parabolic 2).subtype

/-- The actual invariant copy of `V₁` inside the restricted representation. -/
def firstFactorSubrepresentation :
    Subrepresentation firstParabolicRepresentation where
  toSubmodule := V₁
  apply_mem_toSubmodule g := by
    intro v hv
    exact (parabolic_two_le_stabilizer_V₁ g.property v).mpr hv

/-- The actual invariant copy of `V₇` inside the restricted representation. -/
def seventhSubrepresentation :
    Subrepresentation firstParabolicRepresentation where
  toSubmodule := V₇
  apply_mem_toSubmodule g := by
    intro v hv
    exact (parabolic_two_le_stabilizer_V₇ g.property v).mpr hv

/-- `V₁` regarded as a subrepresentation of the restricted action on `V₇`. -/
def firstInsideSeventh :
    Subrepresentation seventhSubrepresentation.toRepresentation where
  toSubmodule := V₁.comap seventhSubrepresentation.toSubmodule.subtype
  apply_mem_toSubmodule g := by
    intro v hv
    change v.1 ∈ V₁ at hv
    change (seventhSubrepresentation.toRepresentation g v).1 ∈ V₁
    exact (parabolic_two_le_stabilizer_V₁ g.property v.1).mpr hv

/-- The literal first chief factor, with its restricted action. -/
noncomputable def firstChiefFactor :
    Representation (ZMod 2) (parabolic 2) firstFactorSubrepresentation.toSubmodule :=
  firstFactorSubrepresentation.toRepresentation

/-- The literal middle chief factor `V₇/V₁`. -/
noncomputable def middleChiefFactor :
    Representation (ZMod 2) (parabolic 2)
      (seventhSubrepresentation.toSubmodule ⧸ firstInsideSeventh.toSubmodule) :=
  firstInsideSeventh.quotientRepresentation

/-- The literal last chief factor `V/V₇`. -/
noncomputable def lastChiefFactor :
    Representation (ZMod 2) (parabolic 2)
      (V ⧸ seventhSubrepresentation.toSubmodule) :=
  seventhSubrepresentation.quotientRepresentation

@[simp] theorem middleChiefFactor_apply_mk (g : parabolic 2)
    (v : seventhSubrepresentation.toSubmodule) :
    middleChiefFactor g (firstInsideSeventh.toSubmodule.mkQ v) =
      firstInsideSeventh.toSubmodule.mkQ
        (seventhSubrepresentation.toRepresentation g v) := rfl

@[simp] theorem lastChiefFactor_apply_mk (g : parabolic 2) (v : V) :
    lastChiefFactor g (seventhSubrepresentation.toSubmodule.mkQ v) =
      seventhSubrepresentation.toSubmodule.mkQ
        (firstParabolicRepresentation g v) := rfl

private theorem firstFactor_nonzero :
    firstFactorSubrepresentation.toSubmodule ≠ ⊥ := by
  intro h
  have hb : basis 0 ∈ V₁ := Submodule.subset_span ⟨0, by decide, rfl⟩
  have hb' : basis 0 ∈ (⊥ : Submodule (ZMod 2) V) := h ▸ hb
  exact basis.ne_zero 0 hb'

/-- The first factor is irreducible because the literal space `V₁` has rank one.
The proof uses the actual basis vector and the actual submodule, rather than a
family label. -/
theorem firstChiefFactor_isIrreducible :
    Representation.IsIrreducible firstChiefFactor := by
  apply (Subrepresentation.irreducible_iff_isAtom firstFactorSubrepresentation).mpr
  refine ⟨?_, ?_⟩
  · intro h
    exact firstFactor_nonzero (congrArg Subrepresentation.toSubmodule h)
  · intro W hW
    by_contra hbot
    have hWbot : W.toSubmodule ≠ ⊥ := by
      intro h
      exact hbot (Subrepresentation.toSubmodule_injective h)
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWbot
    have hdim : Module.finrank (ZMod 2) firstFactorSubrepresentation.toSubmodule = 1 := by
      change Module.finrank (ZMod 2) V₁ = 1
      exact standard_dimensions.1
    have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hdim (hW.le hv) hv0
    have heqsub : W.toSubmodule = firstFactorSubrepresentation.toSubmodule := by
      apply le_antisymm (show W.toSubmodule ≤ firstFactorSubrepresentation.toSubmodule from hW.le)
      rw [hspan]
      exact Submodule.span_le.mpr (fun x hx => by
        rcases hx with rfl
        exact hv)
    exact hW.ne (Subrepresentation.toSubmodule_injective heqsub)

/-- The already established strict invariant chain, attached to the actual
restricted representation. -/
theorem firstParabolic_strict_invariant_chain :
    (⊥ : Submodule (ZMod 2) V) < V₁ ∧ V₁ < V₇ ∧ V₇ < ⊤ :=
  standard_chief_chain_strict

private theorem irreducible_of_equiv
    {W X : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) (parabolic 2) W}
    {σ : Representation (ZMod 2) (parabolic 2) X}
    (e : ρ.Equiv σ) (hσ : Representation.IsIrreducible σ) :
    Representation.IsIrreducible ρ := by
  let f := IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap
  let ef := LinearEquiv.ofBijective f (show Function.Bijective f from e.toLinearEquiv.bijective)
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact ef.isSimpleModule_iff.mpr
    ((Representation.irreducible_iff_isSimpleModule_asModule σ).mp hσ)

/- A checked model equivalence is enough to transport irreducibility to the
   literal middle factor.  The equivalence argument is retained in the theorem
   interface so that a model cannot be replaced by a dimension assertion. -/
theorem middleChiefFactor_isIrreducible_of_equiv
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    {σ : Representation (ZMod 2) (parabolic 2) X}
    (e : middleChiefFactor.Equiv σ)
    (hσ : Representation.IsIrreducible σ) :
    Representation.IsIrreducible middleChiefFactor :=
  irreducible_of_equiv e hσ

/- A checked model equivalence is enough to transport irreducibility to the
   literal final factor. -/
theorem lastChiefFactor_isIrreducible_of_equiv
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    {σ : Representation (ZMod 2) (parabolic 2) X}
    (e : lastChiefFactor.Equiv σ)
    (hσ : Representation.IsIrreducible σ) :
    Representation.IsIrreducible lastChiefFactor :=
  irreducible_of_equiv e hσ

/- The final source assembly uses these model facts together with the literal
   chain above.  Keeping this consumer explicit prevents the model assumptions
   from being mistaken for consequences of strictness or invariance. -/
theorem exteriorStabilizer_V₁_chief_chain_with_factors
    (hmiddle : Representation.IsIrreducible middleChiefFactor)
    (hlast : Representation.IsIrreducible lastChiefFactor) :
    exteriorStabilizer V₁ = parabolic 2 ∧
      ((⊥ : Submodule (ZMod 2) V) < V₁ ∧ V₁ < V₇ ∧ V₇ < ⊤) ∧
      exteriorStabilizer V₁ ≤ exteriorStabilizer V₇ ∧
      Representation.IsIrreducible firstChiefFactor ∧
      Representation.IsIrreducible middleChiefFactor ∧
      Representation.IsIrreducible lastChiefFactor := by
  exact ⟨exteriorStabilizer_V₁_eq_parabolic,
    standard_chief_chain_strict, standard_chief_chain_invariant,
    firstChiefFactor_isIrreducible, hmiddle, hlast⟩

end
end Representation.SL5ExteriorSquare
