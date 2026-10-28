module

public import Theory.SpecificGroups.Tits.RecognitionLocalData
public import Theory.SpecificGroups.Tits.RecognitionLocalSylowRelations
public import Theory.SpecificGroups.Tits.RecognitionLocalConjugationRelations

/-!
# The local algebra in Parrott's recognition argument

The supplied local equations imply all 36 presentation relators other than
VI(i), the eighth-power braid relation. The proof combines the Sylow word
calculations for groups I–V with the power and conjugation calculations for
groups VI–VIII. Consequently the full presentation is equivalent, under these
local equations, to the single remaining braid relation.

This interface also re-exports the proved word identities r₃ = t, r₅ = z,
r₇ = xbcwt and s₇r₇ = wuvz. The definitions and word calculations live in
`RecognitionLocalData`, shared by the two independent relator calculations.

The inputs are the unprimed source equations (1)–(26), elementary relations
for E and F, and generator power and centrality equations. They assert no
existence of witnesses and impose no global relation (rs)⁸ = 1.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§§3 and 6, pp.678–682 and 684. The exact conventions and scan corrections
are recorded in `refs/original/n-group-global/parrott-tits-presentation.md`.
-/

namespace Tits.ParrottLocalRelations

variable {G : Type*} [Group G] {z t v u w a b c d x y r s : G}
variable (h : ParrottLocalRelations z t v u w a b c d x y r s)
include h

/-- The source local equations imply all 36 relators other than VI(i).
No eighth-power relation or existence of local witnesses is assumed. -/
public theorem relators_except_braid (i : ParrottRelatorIndex)
    (hi : i ≠ .vi_r1_r8) :
    FreeGroup.lift (parrottRecognitionWords z t v u w a b c d x y r s)
      (parrottRelator i) = 1 := by
  cases i
  all_goals first
    | exact (hi rfl).elim
    | (apply h.relators_I_V; decide)
    | (apply h.relators_VI_VIII_except_braid; decide)

/-- For the supplied local configuration, the only remaining condition for
the full presentation is the eighth-power relation. Its proof belongs to the
recognition argument using both involution centralizers. -/
public theorem satisfiesParrottRelations_iff :
    SatisfiesParrottRelations (parrottRecognitionWords z t v u w a b c d x y r s) ↔
      (r * s) ^ 8 = 1 := by
  rw [Tits.satisfiesParrottRelations_iff_except_braid]
  exact and_iff_right (h.relators_except_braid)

end Tits.ParrottLocalRelations
