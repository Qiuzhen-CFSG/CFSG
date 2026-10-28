module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Odd.PrimeCover
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Odd.UnitaryThree
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Odd.DegreeThreeCenters
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Odd.PSL2Parameters
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Odd.PSL3Parameters
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Odd.PSU3Parameters

/-!
# Assembly of the odd-characteristic branches of 1.1.5

The action calculations retain the original marked involution. The proved
fixed-group parameter exclusions and central-cover exclusions give the
three source families the canonical row (e), the derived G₂(2)
case of row (a), or the PSL₂(9) overlap delegated to the alternating argument.
The actual field witnesses rule out exponent zero and the solvable PSL₂(3).

The final `MarkedInvolution.odd` discharges the prime-field arithmetic,
square-field exclusion, both large-prime A₂ exclusions, and both
degree-three cover exclusions. The original conditional assembly remains
available separately. The only overlap is PSL₂(9), whose marked alternating
comparison belongs to the alternating-family argument.

Source: Aschbacher--Smith, proof of 1.1.5(3), printed pp.502--503,
especially the odd-characteristic paragraph on p.503.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
open Chapter15.Section03.Candidates.ComponentStructure
variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
variable {α : MulAut L} {P : Sylow 2 L}

/-- Conditional final assembly with the missing model and covering theorems
fully exposed. The only overlap in its conclusion is the source's PSL₂(9). -/
theorem MarkedInvolution.odd_of_parameters_and_centers
    (d : MarkedInvolution α P)
    (hprime : ∀ p : ℕ, p.Prime → Odd p →
      ClassicalGroup.IsPSL (L ⧸ center L) 2 p → IsFermatOrMersennePrime p)
    (hsquare : ∀ p : ℕ, p.Prime → Odd p → 3 < p →
      ClassicalGroup.IsPSL (L ⧸ center L) 2 (p ^ 2) → False)
    (hlinear : ∀ p : ℕ, p.Prime → Odd p →
      ClassicalGroup.IsPSL (L ⧸ center L) 3 p → p = 3)
    (hunitary : ∀ p : ℕ, p.Prime → Odd p →
      ClassicalGroup.IsPSU (L ⧸ center L) 3 p → p = 3)
    (hlinearCenter : ClassicalGroup.IsPSL (L ⧸ center L) 3 3 → center L = ⊥)
    (hunitaryCenter : ClassicalGroup.IsPSU (L ⧸ center L) 3 3 → center L = ⊥)
    (h : ChapterA.Section02.IsTheoremCOddModel (L ⧸ center L)) :
    ModelAction115 L α ∨ ClassicalGroup.IsPSL (L ⧸ center L) 2 9 := by
  cases h with
  | linear_two p e hp ho he hm =>
    rcases linear_two_exponent ho he hm with ⟨he1, _⟩ | he2
    · subst e
      simp only [pow_one] at hm
      exact Or.inl (d.linear_two_prime (hprime p hp ho hm) ho hm)
    · subst e
      by_cases hp3 : p = 3
      · exact Or.inr (by simpa only [hp3, show 3 ^ 2 = 9 from rfl] using hm)
      · have h2 := hp.two_le
        have hodd := Nat.odd_iff.mp ho
        exact (hsquare p hp ho (by omega) hm).elim
  | linear_three p hp ho hm =>
    have he := hlinear p hp ho hm
    subst p
    exact Or.inl (d.linear_three_three_of_center_eq_bot hm (hlinearCenter hm))
  | unitary_three p hp ho hm =>
    have he := hunitary p hp ho hm
    subst p
    exact Or.inl (d.unitary_three_three_of_center_eq_bot hm (hunitaryCenter hm))

/-- The complete odd-characteristic branch of 1.1.5(3), retaining the
original action and Sylow subgroup. Every parameter and covering premise
is discharged; only the source's PSL₂(9) alternating overlap is returned. -/
theorem MarkedInvolution.odd (d : MarkedInvolution α P)
    (h : ChapterA.Section02.IsTheoremCOddModel (L ⧸ center L)) :
    ModelAction115 L α ∨ ClassicalGroup.IsPSL (L ⧸ center L) 2 9 := by
  exact d.odd_of_parameters_and_centers
    (fun _ hp ho => d.linear_two_prime_parameter hp ho)
    (fun _ hp ho => d.linear_two_square_excluded hp ho)
    d.linear_three_parameters d.unitary_three_parameter
    linear_three_three_center_eq_bot unitary_three_three_center_eq_bot h

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
