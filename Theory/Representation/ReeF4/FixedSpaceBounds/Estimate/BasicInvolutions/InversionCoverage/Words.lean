module

public import Theory.SpecificGroups.Tits.Presentation

/-!
# The marked order-thirteen witness word

The product of an involution with a conjugate of itself is inverted by that
involution. Here the involution is Parrott's s₄ and the conjugator is an
explicit word in s₅, r₁ and r₈. Its order is certified in `ThirteenCertificate`
and transported into the actual binary Ree group in `Witnesses`.

Source: Parrott (1972), section 5, p.683, for the generators;
Guralnick--Malle, *Classification of 2F-modules, II*, Lemma 8.8, p.57,
for the inversion argument. The word was found in the repository's checked
permutation realization; no search result is assumed as a theorem.
-/

@[expose] public section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage
open Tits

def thirteenConjugator {G : Type*} [Group G]
    (g : ParrottGenerator → G) : G :=
  g .s5 * g .r1 * g .r8 * g .r1 * g .r8 * g .s5 * g .r1 * g .r8 * g .r1

def thirteenWord {G : Type*} [Group G] (g : ParrottGenerator → G) : G :=
  g .s4 * (thirteenConjugator g * g .s4 * (thirteenConjugator g)⁻¹)

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage
