module

public import Theory.Representation.SubspaceQuotient
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.RepresentationTheory.Character

/-!
# Finite composition series and additive traces

A finite-dimensional representation has a finite series obtained by taking a
simple invariant subspace and continuing in its literal quotient. The recorded
factors are actual representations, and both their natural dimensions and their
field-valued traces add to those of the original representation.

Trace additivity uses a linear section of the quotient map, followed by cyclic
invariance of trace. The section need not intertwine the group action. Existence
of a series follows by induction on dimension, without semisimplicity.

Source: Feit, *The Representation Theory of Finite Groups*, I.1 and I.17;
used for the simple-submodule step of VII.2.25, printed p.304.
-/

public section
noncomputable section
universe u v

open scoped BigOperators
namespace Representation
variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ρ : Representation K G V)

/-- Trace is additive for an invariant subspace and its literal quotient action. -/
theorem character_eq_subrepresentation_add_quotient (U : Subrepresentation ρ) :
    ρ.character = U.toRepresentation.character + U.quotientRepresentation.character := by
  obtain ⟨s, hs⟩ := U.toSubmodule.mkQ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr U.toSubmodule.mkQ_surjective)
  have hs' (x) : U.toSubmodule.mkQ (s x) = x := LinearMap.congr_fun hs x
  let P : V →ₗ[K] U.toSubmodule := (LinearMap.id - s.comp U.toSubmodule.mkQ).codRestrict
    U.toSubmodule (by
      intro x
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change U.toSubmodule.mkQ (x - s (U.toSubmodule.mkQ x)) = 0
      rw [map_sub, hs', sub_self])
  have hP (x : U.toSubmodule) : P x = x := by
    apply Subtype.ext
    change (x : V) - s (U.toSubmodule.mkQ x) = x
    rw [show U.toSubmodule.mkQ x = 0 from (Submodule.Quotient.mk_eq_zero _).mpr x.property, map_zero, sub_zero]
  have hsplit : U.toSubmodule.subtype.comp P + s.comp U.toSubmodule.mkQ =
      LinearMap.id := by
    ext x
    exact sub_add_cancel _ _
  funext g
  change LinearMap.trace K V (ρ g) =
    LinearMap.trace K U.toSubmodule (U.toRepresentation g) +
      LinearMap.trace K (V ⧸ U.toSubmodule) (U.quotientRepresentation g)
  have hf : ρ g = ((ρ g).comp U.toSubmodule.subtype).comp P +
      ((ρ g).comp s).comp U.toSubmodule.mkQ := by
    rw [LinearMap.comp_assoc, LinearMap.comp_assoc, ← LinearMap.comp_add, hsplit,
      LinearMap.comp_id]
  rw [hf, map_add]
  congr 1
  · rw [LinearMap.trace_comp_comm']
    apply congrArg (LinearMap.trace K U.toSubmodule)
    ext x
    exact congrArg Subtype.val (hP (U.toRepresentation g x))
  · rw [LinearMap.trace_comp_comm']
    apply congrArg (LinearMap.trace K (V ⧸ U.toSubmodule))
    apply LinearMap.ext
    intro x
    change U.toSubmodule.mkQ (ρ g (s x)) = U.quotientRepresentation g x
    rw [← Subrepresentation.quotientRepresentation_mk, hs']
end Representation

namespace Representation.CompositionSeriesTrace
variable {K : Type u} {G : Type v} [Field K] [Group G]

/-- A finite composition series, built by successive actual simple submodules
and their literal quotients. The family lists its simple factors in order. -/
inductive FiniteSeries : (M : FDRep K G) → {n : ℕ} → (Fin n → FDRep K G) → Prop
  | zero (M : FDRep K G) [Subsingleton M] : FiniteSeries M (Fin.elim0)
  | step (M : FDRep K G) (U : Subrepresentation M.ρ)
      (simple : IsIrreducible U.toRepresentation) {n : ℕ} {F : Fin n → FDRep K G}
      (rest : FiniteSeries (FDRep.of U.quotientRepresentation) F) :
      FiniteSeries M (Fin.cons (FDRep.of U.toRepresentation) F)

/-- Every finite-dimensional representation has a finite composition series. -/
theorem exists_finiteSeries (M : FDRep K G) :
    ∃ (n : ℕ) (F : Fin n → FDRep K G), FiniteSeries M F := by
  generalize hd : Module.finrank K M = d
  induction d using Nat.strong_induction_on generalizing M with
  | h d ih =>
    cases subsingleton_or_nontrivial M with
    | inl h =>
      let := h
      exact ⟨0, Fin.elim0, .zero M⟩
    | inr h =>
      let := h
      obtain ⟨U, hU⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional M.ρ
      let := hU
      have : Nontrivial U.toSubmodule :=
        Subrepresentation.irreducible_module_nontrivial U.toRepresentation
      have hpos := Module.finrank_pos (R := K) (M := U.toSubmodule)
      have hsum := U.toSubmodule.finrank_quotient_add_finrank
      have hlt : Module.finrank K (M ⧸ U.toSubmodule) < d := by omega
      obtain ⟨n, F, hF⟩ := ih _ hlt (FDRep.of U.quotientRepresentation) rfl
      exact ⟨n + 1, _, .step M U hU hF⟩

/-- Every listed factor is an actual irreducible representation. -/
theorem FiniteSeries.simple {M : FDRep K G} {n : ℕ} {F : Fin n → FDRep K G}
    (h : FiniteSeries M F) : ∀ i, IsIrreducible (F i).ρ := by
  induction h with
  | zero => exact fun i => Fin.elim0 i
  | step M U hU hF ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hU
    · exact ih j

/-- The character is the sum of the characters of the literal simple quotients. -/
theorem FiniteSeries.character_sum {M : FDRep K G} {n : ℕ} {F : Fin n → FDRep K G}
    (h : FiniteSeries M F) : character M.ρ = ∑ i, character (F i).ρ := by
  induction h with
  | zero M =>
    simp only [Fin.sum_univ_zero]
    funext g
    change LinearMap.trace K M _ = 0
    exact (congrArg (LinearMap.trace K M) (Subsingleton.elim (M.ρ g) 0)).trans (map_zero _)
  | @step M U hU n F hF ih =>
    rw [Fin.sum_univ_succ]
    change U.quotientRepresentation.character = ∑ i, character (F i).ρ at ih
    exact (character_eq_subrepresentation_add_quotient M.ρ U).trans (congrArg (U.toRepresentation.character + ·) ih)

/-- Natural dimensions add along the same composition series. -/
theorem FiniteSeries.dimension_sum {M : FDRep K G} {n : ℕ} {F : Fin n → FDRep K G}
    (h : FiniteSeries M F) : Module.finrank K M = ∑ i, Module.finrank K (F i) := by
  induction h with
  | zero M => simp [Module.finrank_zero_of_subsingleton]
  | @step M U hU n F hF ih =>
    rw [Fin.sum_univ_succ]
    change Module.finrank K M = Module.finrank K U.toSubmodule + ∑ i, Module.finrank K (F i)
    rw [← ih]
    exact (add_comm _ _).trans U.toSubmodule.finrank_quotient_add_finrank |>.symm
end Representation.CompositionSeriesTrace
