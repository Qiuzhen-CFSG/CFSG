module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.OffenderModels.StrongSections.Constituents
public import Mathlib.Order.OrderIsoNat

/-!
# A chief flag in the actual submodule

A finite-dimensional binary representation admits an exhaustive finite flag of
literal invariant subspaces. Adjacent terms cover one another in the invariant
subspace lattice, so their literal quotients are irreducible for the whole actor.
This makes no assertion about irreducibility after restriction to the component.

The flag is constant after its last term, hence monotone on all natural numbers.
It will carry the constituent classification in Aschbacher–Smith 13.8.25,
printed p.960 (1 March 2004 manuscript).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections.SourceConstituents
open Representation Representation.BinaryOffender
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) H U)

omit [FiniteDimensional (ZMod 2) U] in
private theorem section_irreducible (L N : Subrepresentation ρ) (hLN : L ⋖ N) :
    IsIrreducible (sectionRepresentation ρ L N) := by
  let Q := sectionLower ρ L N
  have hQ : Q.toSubmodule ≠ ⊤ := by
    intro he
    apply hLN.ne
    apply le_antisymm hLN.le
    intro v hv
    have hw : (⟨v, hv⟩ : N.toSubmodule) ∈ Q.toSubmodule := he.symm ▸ Submodule.mem_top
    exact hw
  let : Nontrivial (N.toSubmodule ⧸ Q.toSubmodule) :=
    Submodule.Quotient.nontrivial_iff.mpr hQ
  refine ⟨?_⟩
  intro S
  let T : Subrepresentation ρ := {
    toSubmodule := (S.toSubmodule.comap Q.toSubmodule.mkQ).map N.toSubmodule.subtype
    apply_mem_toSubmodule g := by
      rintro _ ⟨v, hv, rfl⟩
      exact ⟨N.toRepresentation g v, S.apply_mem_toSubmodule g hv, rfl⟩ }
  have hLT : L ≤ T := by
    intro v hv
    refine ⟨⟨v, hLN.le hv⟩, ?_, rfl⟩
    change Q.toSubmodule.mkQ ⟨v, hLN.le hv⟩ ∈ S.toSubmodule
    have hz : Q.toSubmodule.mkQ ⟨v, hLN.le hv⟩ = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hv
    rw [hz]
    exact S.toSubmodule.zero_mem
  have hTN : T ≤ N := by
    rintro _ ⟨v, _, rfl⟩
    exact v.property
  have hcases : T = L ∨ T = N := by
    by_cases he : T = L
    · exact Or.inl he
    · exact Or.inr (eq_of_le_of_not_lt hTN (fun ht => hLN.2 (lt_of_le_of_ne hLT (Ne.symm he)) ht))
  rcases hcases with he | he
  · left
    apply Subrepresentation.toSubmodule_injective
    apply le_bot_iff.mp
    intro s hs
    obtain ⟨v, rfl⟩ := Q.toSubmodule.mkQ_surjective s
    have hv : (v : U) ∈ T := ⟨v, hs, rfl⟩
    rw [he] at hv
    exact (Submodule.Quotient.mk_eq_zero _).mpr hv
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro s _
    obtain ⟨v, rfl⟩ := Q.toSubmodule.mkQ_surjective s
    have hv : (v : U) ∈ T := he.symm ▸ v.property
    obtain ⟨w, hw, hew⟩ := hv
    have h : w = v := Subtype.ext hew
    exact h ▸ hw

/-- Construct the exhaustive H-chief flag, without classifying its factors. -/
theorem exists_chief_flag : ∃ (n : ℕ) (c : ℕ → Subrepresentation ρ),
    Monotone c ∧ c 0 = ⊥ ∧ c n = ⊤ ∧ ∀ i < n,
      IsIrreducible (sectionRepresentation ρ (c i) (c (i + 1))) := by
  classical
  let : Finite U := Module.finite_of_finite (ZMod 2)
  let : Finite (Subrepresentation ρ) := Finite.of_injective
    (fun S : Subrepresentation ρ => (S : Set U)) SetLike.coe_injective
  obtain ⟨a, ha, n, hn, hc⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le
      (show (⊥ : Subrepresentation ρ) ≤ ⊤ from bot_le)
  let c : ℕ → Subrepresentation ρ := fun i => a (min i n)
  have hmono : Monotone c := by
    apply monotone_nat_of_le_succ
    intro i
    by_cases hi : i < n
    · simpa [c, Nat.min_eq_left (Nat.le_of_lt hi), Nat.min_eq_left hi] using (hc i hi).le
    · have hni : n ≤ i := by omega
      simp only [c, Nat.min_eq_right hni, Nat.min_eq_right (hni.trans (Nat.le_succ i))]
      exact le_rfl
  refine ⟨n, c, hmono, ?_, ?_, ?_⟩
  · simpa [c] using ha
  · simpa [c] using hn
  · intro i hi
    change IsIrreducible (sectionRepresentation ρ (a (min i n)) (a (min (i + 1) n)))
    rw [Nat.min_eq_left (by omega : i ≤ n), Nat.min_eq_left (by omega : i + 1 ≤ n)]
    exact section_irreducible ρ (a i) (a (i + 1)) (hc i hi)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OffenderModels.StrongSections.SourceConstituents
