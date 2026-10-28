module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.Suzuki
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# Exceptional-family reductions for B.1.13

The Suzuki clause identifies the original finite quasisimple component:
cyclic odd Sylow subgroups and trivial two-core remove its entire center.
The small derived symplectic clause identifies the literal projective
commutator quotient with A₆ through the existing six-letter polar action.
Both are unconditional branches of the required recognition alternative;
neither needs an assumption about the component's selected FF action.

`exceptional_quotient_reduction` consumes exactly the exceptional part of
the full carrier catalogue. It retains every unresolved family with its
actual isomorphism and original parameter restrictions, including all three
remaining small derived carriers. This is a reduction, not a proof of the
general FF classification. The missing representation and covering steps
must still be proved for the residual branches.

Source: Aschbacher–Smith, B.1.13, printed pp.73–74 (PDF pp.84–85), citing
Guralnick–Malle, *Classification of 2F-modules, II*, Table 2,
DOI 10.1515/9783110198126.117. No SQTK or Chapter B.4 hypothesis is used.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional

variable {L : Type*} [Group L]

/-- The small symplectic catalogue row gives the genuine alternating quotient,
with the commutator taken after the projective central quotient. -/
theorem symplectic_derived_recognition
    (h : Nonempty (L ⧸ center L ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) :
    ∃ n : ℕ, 5 ≤ n ∧ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin n)) := by
  obtain ⟨e⟩ := h
  exact ⟨6, by decide, ⟨e.trans
    Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩⟩

/-- Prune the symplectic alias, retaining all three other concrete small carriers. -/
theorem smallDerived_reduction (h : KnownSimple.IsSmallDerivedCarrier (L ⧸ center L)) :
    (∃ n : ℕ, 5 ≤ n ∧ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin n))) ∨
      Nonempty (L ⧸ center L ≃* commutator (Atlas.G2.Model (ZMod 2))) ∨
      Nonempty (L ⧸ center L ≃* commutator (Atlas.ReeG2.Model (ZMod 3) 0)) ∨
      Nonempty (L ⧸ center L ≃* Tits.ParrottGroup) := by
  cases h with
  | symplectic e => exact Or.inl (symplectic_derived_recognition e)
  | g2 e => exact Or.inr (Or.inl e)
  | ree e => exact Or.inr (Or.inr (Or.inl e))
  | tits e => exact Or.inr (Or.inr (Or.inr e))

/-- Apply the two completed branches to the literal exceptional catalogue input.
The residual disjunction is the remaining classification obligation. -/
theorem exceptional_quotient_reduction [Finite L] [IsQuasisimple L]
    (hc : pCore 2 L = ⊥)
    (h : KnownSimple.IsG2Carrier (L ⧸ center L) ∨
      (∃ m : ℕ, 1 ≤ m ∧ Nonempty
        (L ⧸ center L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∨
      KnownSimple.IsExceptionalExtensionModel (L ⧸ center L) ∨
      Triality.Standard.IsTrialityGroup (L ⧸ center L) ∨
      ReeF4.IsReeF4Model (L ⧸ center L) ∨
      KnownSimple.IsSmallDerivedCarrier (L ⧸ center L)) :
    (∃ m : ℕ, 1 ≤ m ∧ Nonempty (L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∨
      (∃ n : ℕ, 5 ≤ n ∧ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin n))) ∨
      KnownSimple.IsG2Carrier (L ⧸ center L) ∨
      KnownSimple.IsExceptionalExtensionModel (L ⧸ center L) ∨
      Triality.Standard.IsTrialityGroup (L ⧸ center L) ∨
      ReeF4.IsReeF4Model (L ⧸ center L) ∨
      Nonempty (L ⧸ center L ≃* commutator (Atlas.G2.Model (ZMod 2))) ∨
      Nonempty (L ⧸ center L ≃* commutator (Atlas.ReeG2.Model (ZMod 3) 0)) ∨
      Nonempty (L ⧸ center L ≃* Tits.ParrottGroup) := by
  rcases h with hg2 | hsz | hex | htr | hree | hsmall
  · exact Or.inr (Or.inr (Or.inl hg2))
  · exact Or.inl (suzuki_recognition hc hsz)
  · exact Or.inr (Or.inr (Or.inr (Or.inl hex)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl htr))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hree)))))
  · rcases smallDerived_reduction hsmall with halt | hrest
    · exact Or.inr (Or.inl halt)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hrest)))))

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional
