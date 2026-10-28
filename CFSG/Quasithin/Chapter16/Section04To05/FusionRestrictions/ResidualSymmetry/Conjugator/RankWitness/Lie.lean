module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Conjugator.ActorGeometry
public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Conjugator.RankWitness.Lie.RankOneReduction

/-!
# Lie-family assembly for the selected-residual rank witness

The root calculations eliminate Suzuki covers and inner binary PSL₂ inverse
actions. The remaining PSL₂ field degree must be even. Assembly retains
the unitary rank-one family, every characteristic-two rank-two alternative
of Theorem C, and both binary higher-linear models.

The theorem below is conditional: the four displayed producers must still
construct actual two-local subgroups, an elementary abelian odd-prime plane,
and its independent commuting actor. It is not a proof of 16.5.6(3) until
those producers are supplied. Abstract residual rows do not identify the
embedded subgroups. In particular, A₄ remains two-perfect without being
perfect, and the PSL₅(2) residual is not assumed to have elementary kernel.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, (E2) and
16.1.2–4, printed pp.1170–1171; 16.5.5–6, printed p.1197.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16

namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.Lie

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}

/-- Exhaustive conditional assembly, with all remaining ambient geometry
obligations explicit. The full source covering restrictions remain in `hL`. -/
theorem witness_of_remaining_families
    (hG : Hypothesis1611 KnownSimple.IsKnownSimple G)
    (d : ResidualInputs T z L g R) (hL : IsEvenTypeLieComponent L)
    (hne : modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
      modifiedCentralizerResidual L (MulAut.conj g z))
    (hlinear : ∀ n : ℕ, 2 ≤ n → Even n →
      ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      (¬ ∃ x : L, L.normalizerMonoidHom
        ⟨MulAut.conj g⁻¹ z, d.inverse_mem_normalizer⟩ = MulAut.conj x) →
      Nonempty (OddRankThreeWitness G))
    (hunitary : ∀ n : ℕ, 2 ≤ n →
      ClassicalGroup.IsPSU (L ⧸ pCore 2 L) 3 (2 ^ n) →
      Nonempty (OddRankThreeWitness G))
    (hrankTwo : ∀ f : ℕ,
      ChapterA.Section02.IsTheoremCRankTwoModel (L ⧸ pCore 2 L) f →
      Nonempty (OddRankThreeWitness G))
    (hhigher : ∀ n : ℕ, (n = 4 ∨ n = 5) →
      ClassicalGroup.IsPSL (L ⧸ pCore 2 L) n 2 →
      Nonempty (OddRankThreeWitness G)) : Nonempty (OddRankThreeWitness G) := by
  rcases hL.1 with hb | ⟨f, hf⟩ | ⟨n, hn, he⟩
  · rcases bender_remaining hG.evenType d hne hb with
      ⟨n, hn, heven, he, houter⟩ | ⟨n, hn, he⟩
    · exact hlinear n hn heven he houter
    · exact hunitary n hn he
  · exact hrankTwo f hf
  · exact hhigher n hn he

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator.Lie
