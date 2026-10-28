module
public import Stellmacher.SectionNine.NineThreeCenterSplitting
public import Stellmacher.SectionNine.NineSevenNormalityObstructions
/-!
# Irreducibility of the initial-orbit center plane

At critical length greater than one, a subgroup of an initial-orbit vertex's
center normalized by its full stabilizer is either trivial or the whole center.
The actual (9.3) gives center order four. Any proper nontrivial subgroup has
order two and, by the three-line geometry, is the center of a neighboring
vertex. The edge center-normality obstruction excludes its normalization by
the entire middle stabilizer.

This is the natural centerplane irreducibility after Stellmacher (9.3), used
in the translation-orbit part of the centralizing-conjugator argument in
(9.9), printed p.56/PDF p.46 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_three_center_irreducible
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (middle : ctx.Γ.Vertex)
    (horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.a middle)
    (J : Subgroup G) (hJ : J ≤ ZAt ctx.Γ middle)
    (hnorm : GAt ctx.Γ middle ≤ Subgroup.normalizer (J : Set G)) :
    J = ⊥ ∨ J = ZAt ctx.Γ middle := by
  obtain ⟨hmodel,hcard⟩ := lemma_nine_three_ambient ctx hb middle horbit
  by_cases hbot : J = ⊥
  · exact Or.inl hbot
  by_cases htop : J = ZAt ctx.Γ middle
  · exact Or.inr htop
  have hpositive := (Subgroup.one_lt_card_iff_ne_bot J).mpr hbot
  have hdiv : Nat.card J ∣ 2^2 := by
    have hh := Subgroup.card_dvd_of_le hJ
    rwa [hcard] at hh
  obtain ⟨power,hpower,hJcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have htwo : Nat.card J = 2 := by
    interval_cases power
    · have hone : Nat.card J = 1 := by simpa using hJcard
      omega
    · simpa using hJcard
    · have heq := Subgroup.eq_of_le_of_card_ge hJ (by rw [hcard,hJcard]; decide)
      exact (htop heq).elim
  obtain ⟨hjoin,hcenters⟩ := nine_seven_center_join ctx middle horbit
  obtain ⟨neighbor,hneighbor,hline⟩ :=
    (nine_seven_center_lines_of_center_join ctx.sectionSeven ctx.Γ middle hmodel hcard
      hjoin hcenters).2.1 J htwo hJ
  apply False.elim
  apply neighbor_center_not_normalized ctx.sectionSeven ctx.Γ middle neighbor hneighbor
  change GAt ctx.Γ middle ≤ Subgroup.normalizer (ZAt ctx.Γ neighbor : Set G)
  rwa [← hline]

end Stellmacher.SectionNine
