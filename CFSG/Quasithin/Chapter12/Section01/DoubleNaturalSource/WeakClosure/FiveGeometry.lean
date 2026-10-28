module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.Offenders
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceFiveActors
public import Theory.ElementaryAbelian.PrimeRankCard

/-!
# The degree-five high-rank offender branch

For the actual automizer representation, H.9.2(5) makes the corank-three
core of every elementary actor of rank at least five equal to the orbit.
E.3.32 puts that same core in a proper relative normalizer. This rules out
the second-stage configuration and reduces the first stage to rank four.

The compatible H.9 source action remains an explicit input. An abstract
isomorphism of the acting group is not substituted for that input.
Source: Aschbacher--Smith, H.9.2(5), 12.1.8 and 12.1.10, pp.390--391,793--794.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation.BinaryOffender BinaryNaturalDual
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterH.NaturalDual
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure
variable {G : Type*} [Group G] [Finite G] {W : Subgroup G} [IsElementaryAbelian 2 W]

/-- H.9.2(5) for a source model of the actual automizer representation.
The representation equality is essential: a group isomorphism alone is insufficient. -/
theorem five_core_eq_orbit
    (S : SourceSetup 5 (Automizer W) (Additive W))
    (hρ : S.representation = automizerRepresentation W)
    (I : Subgroup (Automizer W)) [IsElementaryAbelian 2 I] (hI : 5 ≤ rank I) :
    automizerDualCore W I 3 = W := by
  have hp : 5 ≤ primeRank 2 I := by
    simpa only [rank, IsElementaryAbelian.log_card_eq_primeRank] using hI
  have hc := (SourceFiveActors.high_rank_family S I hp).2
  rw [hρ] at hc
  have ha : multiplicativeAction ((automizerRepresentation W).comp I.subtype) =
      ((Automizer W).subtype.comp I.subtype) := by
    ext a w
    rfl
  rw [ha] at hc
  have hc' : dualGeneratedCore ((Automizer W).subtype.comp I.subtype) 3 = (⊤ : Subgroup W) := hc
  unfold automizerDualCore
  rw [hc']
  apply le_antisymm
  · rintro _ ⟨w, _, rfl⟩
    exact w.property
  · intro w hw
    exact ⟨⟨w, hw⟩, Subgroup.mem_top _, rfl⟩

/-- The high-image-rank branch of 12.1.8 for degree five is impossible. -/
theorem five_first_rank_le_four
    (S : SourceSetup 5 (Automizer W) (Additive W))
    (hρ : S.representation = automizerRepresentation W)
    {g : G} (C : ConjugateConfiguration W g 1 5) :
    rank (inducedAutomizer W (offenderNormalizer W g)) ≤ 4 := by
  by_contra! hr
  let := offender_inducedAutomizer_elementary W g
  exact C.core_ne_orbit (by decide : 1 + 3 < 5)
    (five_core_eq_orbit S hρ _ (by omega))

/-- The degree-five geometry closes the corank-two configuration in 12.1.10. -/
theorem five_second_configuration_false
    (S : SourceSetup 5 (Automizer W) (Additive W))
    (hρ : S.representation = automizerRepresentation W)
    {g : G} (C : ConjugateConfiguration W g 2 7) : False := by
  let := offender_inducedAutomizer_elementary W g
  exact C.core_ne_orbit (by decide : 2 + 3 < 7)
    (five_core_eq_orbit S hρ _ C.rank_lower)

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure
