module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Models
/-!
# The component-sieve fields actually established from the E.6 source

This five-way predicate preserves the full Borel, symplectic and alternating
records and the exact linear-four and odd models, action corank and global
rank. Only U = C_V(L) is omitted from the latter two rows: their existing
source producers do not establish that equality for arbitrary U in Γ.
Full original records convert to this interface without changing those APIs.

The E.6.11 minimum supplies its own fixed-space equality by maximality.
The E.6.19 and E.6.22 inspections use the actual models and original actor,
so they can consume this interface without an unproved kernel equality.
Source: Aschbacher–Smith, E.6.8 and E.6.11, printed pp.247–250.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] {M V U Q L : Subgroup G}

/-- The exact proved five-way model output, without two unestablished kernel identities. -/
@[expose] def AdequateComponentAlternatives (M V U Q L : Subgroup G) : Prop :=
  (∃ n, BorelAlternative M V U L n) ∨
  (∃ n, SymplecticAlternative M V U L n) ∨
  (ClassicalGroup.IsPSL L 4 2 ∧
    Nonempty ((↥(L ⊔ Q) ⧸ pCore 2 ↥(L ⊔ Q)) ≃* Equiv.Perm (Fin 8)) ∧
    actionCorank V L = 1 ∧ globalR V = 1) ∨
  AlternatingAlternative M V U L ∨
  (((∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL L 2 p) ∨
    ClassicalGroup.IsPSL L 3 3 ∨ Nonempty (L ≃* Sporadic.Mathieu.M11)) ∧
    actionCorank V L = 1 ∧ globalR V = 1)

/-- Forget only the two kernel-equality fields. -/
theorem ComponentAlternatives.adequate (ha : ComponentAlternatives M V U Q L) :
    AdequateComponentAlternatives M V U Q L := by
  rcases ha with hb | hs | h4 | ha | ho
  · exact Or.inl hb
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr (Or.inl ⟨h4.model,h4.quotient,h4.dimension,h4.global_rank⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ho.model,ho.dimension,ho.global_rank⟩)))

/-- The minimum consumer needs only the two torus branches or global rank one. -/
theorem AdequateComponentAlternatives.borel_symplectic_or_rank_one
    (ha : AdequateComponentAlternatives M V U Q L) :
    (∃ n, BorelAlternative M V U L n) ∨
      (∃ n, SymplecticAlternative M V U L n) ∨ globalR V = 1 := by
  rcases ha with hb | hs | h4 | ha | ho
  · exact Or.inl hb
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr h4.2.2.2)
  · exact Or.inr (Or.inr ha.global_rank)
  · exact Or.inr (Or.inr ho.2.2)
end CFSG.Quasithin.ChapterE.Section06.Components
