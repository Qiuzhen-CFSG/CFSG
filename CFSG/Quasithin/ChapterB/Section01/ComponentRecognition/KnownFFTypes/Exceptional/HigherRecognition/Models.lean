module

public import CFSG.KnownSimple.CarrierCatalogue

/-!
# Concrete higher exceptional quotient families

Partition the literal exceptional carrier witnesses into split even-field,
twisted even-field, and cross-characteristic branches for binary FF recognition.
All predicates retain the catalogue's actual multiplicative equivalences.
The small derived endpoints belong to their separate catalogue branch.

Source: Guralnick–Malle, *Classification of 2F-modules, I*, Proposition 4.6;
*II*, Theorem B, Sections 8–9. See `Source.md` for the recovered author sources
and for the distinction between F-modules and 2F-modules. This partition
does not prove a representation exclusion.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher

variable (Q : Type*) [Group Q]

/-- The complete input of the higher exceptional branch, using genuine carriers. -/
def IsHigherQuotient : Prop :=
  KnownSimple.IsExceptionalExtensionModel Q ∨
    Triality.Standard.IsTrialityGroup Q ∨ ReeF4.IsReeF4Model Q

/-- The four split families in the defining characteristic of a binary module. -/
def IsEvenSplitQuotient : Prop :=
  ∃ q : ℕ, Even q ∧ (ExceptionalGroup.IsF4 Q q ∨ ExceptionalGroup.IsE6 Q q ∨
    ExceptionalGroup.IsE7 Q q ∨ ExceptionalGroup.IsE8 Q q)

/-- The three genuinely twisted families in characteristic two. -/
def IsEvenTwistedQuotient : Prop :=
  (∃ q : ℕ, Even q ∧ ExceptionalGroup.IsTwistedE6 Q q) ∨
    (∃ q : ℕ, Even q ∧ Triality.Standard.IsTrialityGroupAt q Q) ∨
    ReeF4.IsReeF4Model Q

/-- All odd-field exceptional inputs, including the entire simple small-Ree range. -/
def IsOddQuotient : Prop :=
  (∃ q : ℕ, Odd q ∧ (ExceptionalGroup.IsF4 Q q ∨ ExceptionalGroup.IsE6 Q q ∨
    ExceptionalGroup.IsE7 Q q ∨ ExceptionalGroup.IsE8 Q q ∨
    ExceptionalGroup.IsTwistedE6 Q q ∨ Triality.Standard.IsTrialityGroupAt q Q)) ∨
    (∃ q : ℕ, ExceptionalGroup.IsReeG2 Q q)

variable {Q} {R : Type*} [Group R]

/-- The input transports by composition of its actual carrier equivalences. -/
theorem IsHigherQuotient.of_mulEquiv (h : IsHigherQuotient Q) (e : R ≃* Q) :
    IsHigherQuotient R := by
  rcases h with h | h | h
  · exact Or.inl (h.of_mulEquiv e)
  · exact Or.inr (Or.inl (h.of_mulEquiv e))
  · exact Or.inr (Or.inr (h.of_mulEquiv e))

/-- Exhaust all six extension constructors and both separate twisted families. -/
theorem higher_quotient_cases (h : IsHigherQuotient Q) :
    IsEvenSplitQuotient Q ∨ IsEvenTwistedQuotient Q ∨ IsOddQuotient Q := by
  rcases h with h | h | h
  · cases h with
    | f4 q h =>
      rcases Nat.even_or_odd q with he | ho
      · exact Or.inl ⟨q, he, Or.inl h⟩
      · exact Or.inr (Or.inr (Or.inl ⟨q, ho, Or.inl h⟩))
    | e6 q h =>
      rcases Nat.even_or_odd q with he | ho
      · exact Or.inl ⟨q, he, Or.inr (Or.inl h)⟩
      · exact Or.inr (Or.inr (Or.inl ⟨q, ho, Or.inr (Or.inl h)⟩))
    | e7 q h =>
      rcases Nat.even_or_odd q with he | ho
      · exact Or.inl ⟨q, he, Or.inr (Or.inr (Or.inl h))⟩
      · exact Or.inr (Or.inr (Or.inl ⟨q, ho, Or.inr (Or.inr (Or.inl h))⟩))
    | e8 q h =>
      rcases Nat.even_or_odd q with he | ho
      · exact Or.inl ⟨q, he, Or.inr (Or.inr (Or.inr h))⟩
      · exact Or.inr (Or.inr (Or.inl ⟨q, ho, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩))
    | twistedE6 q h =>
      rcases Nat.even_or_odd q with he | ho
      · exact Or.inr (Or.inl (Or.inl ⟨q, he, h⟩))
      · exact Or.inr (Or.inr (Or.inl
          ⟨q, ho, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩))
    | reeG2 q h => exact Or.inr (Or.inr (Or.inr ⟨q, h⟩))
  · obtain ⟨P, hP⟩ := h
    have hm : Triality.Standard.IsTrialityGroupAt P.q Q := ⟨P, rfl, hP⟩
    rcases Nat.even_or_odd P.q with he | ho
    · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨P.q, he, hm⟩)))
    · exact Or.inr (Or.inr (Or.inl
        ⟨P.q, ho, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hm))))⟩))
  · exact Or.inr (Or.inl (Or.inr (Or.inr h)))

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher
