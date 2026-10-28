module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.LocalClasses
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.PrimeValues
public import Theory.Character.UniqueDegreeRationality

/-!
# Conditional assembly of Janko's degree-21 character

The local centralizer census proves all even-order alternatives. An explicit
odd-order spectrum then forces the five- and eleven-centralizers to have
prime order. Uniqueness at degree 21 makes the genuine irreducible character
integer-valued by Galois conjugation. The prime congruence and column bound
give its values at five and eleven, and defect-zero vanishing gives zero at
seven. This supplies every order/value clause of `Degree21Character`.

This conditional interface keeps character construction, the degree bounds,
and the odd-order spectrum independent. The parent `Degree21` module
discharges all these premises from the original local recognition inputs;
no character certificate is assumed as part of its input.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Sections 6--7, especially pp.15--16,
DOI 10.1016/0021-8693(68)90002-1.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21
open LocalModelDichotomy CaseII
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Assemble the character after supplying its actual irreducibility, local
values, degree bounds, and odd-order group facts. -/
public theorem nonempty_of_character_and_odd_structure
    (D : LocalData G) (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (hcard : Nat.card G = 443520)
    (χ : ClassFunction G) (hχ : IsIrreducibleCharacter χ) (hloc : HasLocalValues D k χ)
    (hmin : ∀ θ : ClassFunction G, IsIrreducibleCharacter θ → θ ≠ 1 →
      (21 : ℝ) ≤ (θ 1).re)
    (huniq : ∀ θ : ClassFunction G, IsIrreducibleCharacter θ → θ 1 = 21 → θ = χ)
    (hodd : ∀ g : G, Odd (orderOf g) →
      orderOf g ∈ ({1, 3, 5, 7, 11} : Finset ℕ)) :
    Nonempty (Degree21Character G) := by
  have hclass : IsClassFunction χ := by
    obtain ⟨n, ρ, _, rfl⟩ := hχ
    exact ρ.char_conj
  have horders := orders_of_odd_orders D k L hodd
  have hi : ∀ g, ∃ a : ℤ, χ g = (a : ℂ) :=
    hχ.integer_of_unique_degree (by simpa [hloc.degree] using huniq)
  refine ⟨{
    chi := χ
    irreducible := hχ
    degree := hloc.degree
    minimum := hmin
    unique := huniq
    values := ?_ }⟩
  intro g
  by_cases heven : Even (orderOf g)
  · rcases even_values D k L hclass hloc g heven with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · have hord := hodd g (Nat.not_even_iff_odd.mp heven)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hord
    rcases hord with ho | ho | ho | ho | ho
    · exact Or.inl ⟨ho, by simpa [orderOf_eq_one_iff.mp ho] using hloc.degree⟩
    · exact Or.inr (Or.inr (Or.inl ⟨ho, value_at_three D k L hclass hloc g ho⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨ho, value_at_five hχ hloc.degree hi g ho (prime_centralizer_card_of_orders hcard horders (Or.inl rfl) g ho)⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨ho, value_at_seven hχ hloc.degree hcard g ho⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨ho, value_at_eleven hχ hloc.degree hi g ho (prime_centralizer_card_of_orders hcard horders (Or.inr rfl) g ho)⟩)))))))

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21
