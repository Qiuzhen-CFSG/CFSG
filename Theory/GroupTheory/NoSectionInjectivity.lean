module
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Injectivity over a quotient without a section

Suppose a homomorphism from a finite group surjects onto a quotient after
composition, with composite kernel of order two. If the quotient map has
no homomorphic section, the original homomorphism is injective. Otherwise
its nontrivial kernel equals the whole composite kernel, and the universal
property of the surjection descends it to a section.

This elementary first-isomorphism argument supplies the injectivity step
for the nonsplit PSL2(3) central cover used in Alperin--Brauer--Gorenstein,
Chapter II, Section 3, Proposition 2. It needs no centrality or finiteness
assumption on the intermediate group.
-/

namespace MonoidHom

/-- A lift with two-element composite kernel is faithful over a nonsplit quotient. -/
public theorem injective_of_comp_ker_card_two_of_no_section
    {B E Q : Type*} [Group B] [Group E] [Group Q] [Finite B]
    (q : E →* Q) (f : B →* E)
    (hsurj : Function.Surjective (q.comp f))
    (hker : Nat.card (q.comp f).ker = 2)
    (hnosection : ¬ ∃ s : Q →* E, q.comp s = MonoidHom.id Q) :
    Function.Injective f := by
  classical
  by_contra hni
  have hle : f.ker ≤ (q.comp f).ker := by
    intro x hx
    change q (f x) = 1
    rw [show f x = 1 from hx, map_one]
  have hcard : Nat.card f.ker = 2 := by
    have hd := Subgroup.card_dvd_of_le hle
    rw [hker] at hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact False.elim (hni ((f.ker_eq_bot_iff).mp (Subgroup.card_eq_one.mp h)))
    · exact h
  have heq : f.ker = (q.comp f).ker :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hker, hcard])
  let s : Q →* E := (q.comp f).liftOfSurjective hsurj ⟨f, heq.ge⟩
  apply hnosection
  refine ⟨s, ?_⟩
  ext x
  obtain ⟨b, rfl⟩ := hsurj x
  change q (s ((q.comp f) b)) = (q.comp f) b
  have hs : s ((q.comp f) b) = f b :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ b
  rw [hs]
  rfl

end MonoidHom

