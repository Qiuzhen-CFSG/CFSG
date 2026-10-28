module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.Data
public import Theory.GroupTheory.PerfectCentralCover

/-!+# Marked M₁ relations in central double covers

The presentation need not be faithful to eliminate a perfect central double
cover. It suffices to prove the twelve local relations after mapping the
presentation into that cover. `BinaryImages` bounds the resulting local image
and uses the checked coset cover to eliminate the full kernel.

The two remaining contracts separate four even words from three odd words.
The latter contract may use the former equations in the same marked image;
its producer can therefore work independently of the even producer. These
are unproved word-identity contracts, not assertions about the multiplier.
Neither contract assumes that the double cover is trivial.

Sources: John Bray's `Held/Model/Source/HeG1-P1.M` and the frozen literal
words in `M1Restriction/Data.lean`; Aschbacher--Smith I.1.1 and I.1.3, p.407.
-/

@[expose] public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction
open Subgroup.CosetWordCertificate PerfectCentralCovering
universe u

/-- All twelve frozen relations hold in the marked image of the presentation. -/
def ImageRelations {E : Type u} [Group E] (h : Presentation →* E) : Prop :=
  ∀ i, h (eval liftedGenerator (relationLetters i)) = 1

/-- The four independent even-word obligations. Entry 5 follows from entry 4. -/
def EvenImageRelations {E : Type u} [Group E] (h : Presentation →* E) : Prop :=
  ∀ i : Fin 12, (i = 4 ∨ i = 6 ∨ i = 10 ∨ i = 11) →
    h (eval liftedGenerator (relationLetters i)) = 1

/-- The three odd-word obligations, with the original generator marking. -/
def OddImageRelations {E : Type u} [Group E] (h : Presentation →* E) : Prop :=
  ∀ i : Fin 12, (i = 7 ∨ i = 8 ∨ i = 9) →
    h (eval liftedGenerator (relationLetters i)) = 1

/-- Even-word input restricted to actual finite perfect central double covers. -/
def BinaryEvenRelations : Prop :=
  ∀ (E : Type u) [Group E] [Finite E] (f : Cover E He),
    Nat.card f.toMonoidHom.ker = 2 →
    ∀ h : Presentation →* E, f.toMonoidHom.comp h = presentationMap →
      EvenImageRelations h

/-- Odd-word input, conditional on the four even equations in the same cover.
All quotient maps and marked generators remain literal. -/
def BinaryOddRelations : Prop :=
  ∀ (E : Type u) [Group E] [Finite E] (f : Cover E He),
    Nat.card f.toMonoidHom.ker = 2 →
    ∀ h : Presentation →* E, f.toMonoidHom.comp h = presentationMap →
      EvenImageRelations h → OddImageRelations h

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction
