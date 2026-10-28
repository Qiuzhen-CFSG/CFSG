module

public import Theory.GroupTheory.CosetWordCertificateBoolean

/-! Kernel-checked five-relator J₃ local coset certificate.
Reproduce with `Theory/SpecificGroups/Janko3/AmalgamPresentation/Coordinates/Nine/Presentation/source/generate.py`; provenance is in `source/README.md`. -/

@[expose] public section
namespace Sporadic.Janko3.AmalgamPresentation.Coordinates.Nine.Presentation.Certificate
open Subgroup.CosetWordCertificate

/-- A balanced lookup between packed pages. -/
def branch {α : Type*} (cutoff : Nat) (left right : Nat → α) (i : Nat) : α :=
  if i < cutoff then left i else right i

/-- Decode one fixed-width entry from a page of 128 entries. -/
def unpack (pages : Nat → Nat) (bits i : Nat) : Nat :=
  (pages (i / 128) >>> (bits * (i % 128))) % (2 ^ bits)

/-- Balanced bounded conjunction, avoiding linear recursion in a long trace. -/
def allBlock (p : Nat → Bool) : Nat → Nat → Bool
  | 0, start => p start
  | depth + 1, start => allBlock p depth start && allBlock p depth (start + 2 ^ depth)

theorem allBlock_spec (p : Nat → Bool) (depth start : Nat)
    (h : allBlock p depth start = true) :
    ∀ n, start ≤ n → n < start + 2 ^ depth → p n = true := by
  induction depth generalizing start with
  | zero =>
    intro n hlo hhi
    have hn : n = start := by omega
    subst n
    exact h
  | succ depth ih =>
    simp only [allBlock, Bool.and_eq_true] at h
    intro n hlo hhi
    rw [Nat.pow_succ, Nat.mul_two] at hhi
    by_cases hn : n < start + 2 ^ depth
    · exact ih start h.1 n hlo hn
    · exact ih (start + 2 ^ depth) h.2 n (by omega) (by omega)

/-- Soundness uses the existing six-rule checker and its actual coset witnesses. -/
theorem block_sound {G α : Type*} [Group G] [BEq α] [LawfulBEq α] [DecidableEq α]
    {C : Context α} {H : Subgroup G} {g : α → G} {ρ : Nat → G}
    (valid : Valid C H g ρ) (fs : Nat → FactData α) (ops : Nat → Instruction α)
    (depth start : Nat) (prior : ∀ n, n < start → Holds H g ρ (fs n))
    (checked : allBlock (fun n => checkBool C fs n (ops n) (fs n)) depth start = true) :
    ∀ n, n < start + 2 ^ depth → Holds H g ρ (fs n) := by
  apply sound_chunk valid fs ops start (start + 2 ^ depth) prior
  intro n hlo hhi
  exact (checkBool_iff C fs n (ops n) (fs n)).mp (allBlock_spec _ _ _ checked n hlo hhi)

end Sporadic.Janko3.AmalgamPresentation.Coordinates.Nine.Presentation.Certificate
