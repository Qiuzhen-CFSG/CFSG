module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.Series
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Order.Atoms

/-!
# From saturated flags to exhaustive invariant-subspace series

A composition flag need not enumerate every invariant subspace. If a finite
saturated flag misses a subspace U, finite dimension gives a competing upper
cover at a flag term: otherwise induction forces every term, including the
whole space, into U. Excluding these competing covers therefore constructs
an `ExhaustiveSeries` without changing any terms or quotient actions.

We also identify the first quotient with its actual subrepresentation and
prove indecomposability when this simple subrepresentation lies in every
nonzero subrepresentation. This uses only the first socle layer.

These are finite-filtration steps for Feit, *The Representation Theory of
Finite Groups*, VII.2.20 and VII.2.23, proof pp.302--303. The cyclic-defect
exclusion of competing covers is a separate source obligation.
-/

public section
noncomputable section

namespace Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    {ρ : Representation K G V} {s : ℕ}

/-- A finite saturated chain from zero to the whole representation. Unlike
`ExhaustiveSeries`, this does not claim to contain every invariant subspace. -/
structure SaturatedFlag (ρ : Representation K G V) (s : ℕ) where
  term : Fin (s + 1) ↪o Subrepresentation ρ
  first : term 0 = ⊥
  last : term (Fin.last s) = ⊤
  step : ∀ i : Fin s, term i.castSucc ⋖ term i.succ

namespace SaturatedFlag

/-- The literal induced action on the successive vector-space quotient. -/
@[expose] def factor (c : SaturatedFlag ρ s) (i : Fin s) :=
  (inside (c.term i.castSucc) (c.term i.succ)).quotientRepresentation

/-- Excluding an alternative upper cover at each flag term makes the flag
exhaustive. Finite dimension supplies a minimal subspace above a given term. -/
theorem surjective_of_unique_covers [FiniteDimensional K V]
    (c : SaturatedFlag ρ s)
    (hc : ∀ (i : Fin s) (W : Subrepresentation ρ),
      c.term i.castSucc ⋖ W → W = c.term i.succ) :
    Function.Surjective c.term := by
  let e : Subrepresentation ρ ↪o Submodule K V :=
    { toFun := Subrepresentation.toSubmodule
      inj' := Subrepresentation.toSubmodule_injective
      map_rel_iff' := Iff.rfl }
  let : WellFoundedLT (Subrepresentation ρ) :=
    (Submodule.finrank_strictMono (K := K) (V := V)).comp e.strictMono |>.wellFoundedLT
  intro U
  by_contra! h
  have hall : ∀ i, c.term i ≤ U := by
    intro i
    induction i using Fin.induction with
    | zero => simp [c.first]
    | succ i ih =>
      obtain ⟨W, hW, hWU⟩ := exists_covBy_le_of_lt (lt_of_le_of_ne ih (h i.castSucc))
      rw [hc i W hW] at hWU
      exact hWU
  exact h (Fin.last s) (le_antisymm (hall _) (by rw [c.last]; exact le_top))

/-- Turn a saturated flag into the exact exhaustive series interface, once
the source no-branching obligation has been discharged. -/
@[expose] def toExhaustive [FiniteDimensional K V] (c : SaturatedFlag ρ s)
    (hc : ∀ (i : Fin s) (W : Subrepresentation ρ),
      c.term i.castSucc ⋖ W → W = c.term i.succ) : ExhaustiveSeries ρ s where
  term := OrderIso.ofSurjective c.term (c.surjective_of_unique_covers hc)

@[simp] theorem toExhaustive_term [FiniteDimensional K V] (c : SaturatedFlag ρ s)
    (hc : ∀ (i : Fin s) (W : Subrepresentation ρ),
      c.term i.castSucc ⋖ W → W = c.term i.succ) (i : Fin (s + 1)) :
    (c.toExhaustive hc).term i = c.term i := rfl

@[simp] theorem toExhaustive_factor [FiniteDimensional K V] (c : SaturatedFlag ρ s)
    (hc : ∀ (i : Fin s) (W : Subrepresentation ρ),
      c.term i.castSucc ⋖ W → W = c.term i.succ) (i : Fin s) :
    (c.toExhaustive hc).factor i = c.factor i := rfl

/-- A missing invariant subspace forces a competing simple extension at
some flag term. This is the finite obstruction used by the socle-layer proof. -/
theorem exists_other_cover_of_not_surjective [FiniteDimensional K V]
    (c : SaturatedFlag ρ s) (h : ¬ Function.Surjective c.term) :
    ∃ (i : Fin s) (W : Subrepresentation ρ),
      c.term i.castSucc ⋖ W ∧ W ≠ c.term i.succ := by
  by_contra! hc
  exact h (c.surjective_of_unique_covers hc)

/-- The first nonzero term is a simple subrepresentation. -/
theorem first_isAtom (c : SaturatedFlag ρ s) (h : 0 < s) :
    IsAtom (c.term (⟨0, h⟩ : Fin s).succ) := by
  apply bot_covBy_iff.mp
  simpa [c.first] using c.step ⟨0, h⟩

/-- Quotienting the first nonzero term by the zero term recovers its actual
representation, with the induced action intertwined by the quotient map. -/
def firstFactorEquiv (c : SaturatedFlag ρ s) (h : 0 < s) :
    (c.factor ⟨0, h⟩).Equiv (c.term (⟨0, h⟩ : Fin s).succ).toRepresentation := by
  let N := inside (c.term (⟨0, h⟩ : Fin s).castSucc)
    (c.term (⟨0, h⟩ : Fin s).succ)
  have hN : N.toSubmodule = ⊥ := by
    ext x
    change (x.val ∈ (c.term (⟨0, h⟩ : Fin s).castSucc)) ↔ x = 0
    rw [show (⟨0, h⟩ : Fin s).castSucc = 0 from rfl, c.first]
    change x.val = 0 ↔ x = 0
    exact ⟨fun hx => Subtype.ext hx, fun hx => congrArg Subtype.val hx⟩
  refine Representation.Equiv.mk (N.toSubmodule.quotEquivOfEqBot hN) ?_
  intro g
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ x =>
    change N.toSubmodule.quotEquivOfEqBot hN
      (N.toSubmodule.mkQ ((c.term (⟨0, h⟩ : Fin s).succ).toRepresentation g x)) =
      (c.term (⟨0, h⟩ : Fin s).succ).toRepresentation g
        (N.toSubmodule.quotEquivOfEqBot hN (N.toSubmodule.mkQ x))
    simp

/-- A simple first term contained in every nonzero subrepresentation prevents
a decomposition into nonzero invariant summands. Seriality is not needed. -/
theorem no_nontrivial_complement_of_simple_socle (c : SaturatedFlag ρ s)
    (hsoc : ∀ (h : 0 < s) (U : Subrepresentation ρ), U ≠ ⊥ →
      c.term (⟨0, h⟩ : Fin s).succ ≤ U)
    (U W : Subrepresentation ρ) (hUW : IsCompl U W) : U = ⊥ ∨ W = ⊥ := by
  by_cases h : 0 < s
  · by_contra! hn
    have hle : c.term (⟨0, h⟩ : Fin s).succ ≤ U ⊓ W :=
      le_inf (hsoc h U hn.1) (hsoc h W hn.2)
    rw [hUW.inf_eq_bot] at hle
    exact (c.first_isAtom h).ne_bot (le_bot_iff.mp hle)
  · have hs : s = 0 := by omega
    subst s
    have heq : (⊥ : Subrepresentation ρ) = ⊤ := c.first.symm.trans c.last
    exact Or.inl (le_bot_iff.mp (heq ▸ le_top))

end SaturatedFlag

end Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules
