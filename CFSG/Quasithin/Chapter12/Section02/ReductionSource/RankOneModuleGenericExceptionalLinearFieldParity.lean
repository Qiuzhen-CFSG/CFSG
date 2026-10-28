module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.Estimates
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldCartan

/-!
# The parity source obligations on the original chosen setup

Compatible Cartans are constructed from the original Chapter 12 hypotheses.
The odd-exponent preparation, representation bound and terminal critical-pair
argument remain three separate source obligations. The conditional assembly
below identifies exactly where they are used, and the intermediate consumer
constructs the faithful non-FF action on the actual specialized U/Z₁.

This module does not assert that any of those three source obligations has
been proved. The unconditional parity theorem remains with their assembly
owner. Source: Aschbacher–Smith, 5.1.17, printed pp.640–642; the application
to 12.2.2 is on printed p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open LinearParity

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- The actual Cartans and the specialized module give a faithful non-FF
action once the independent preparation and displacement sources are supplied. -/
theorem rankOne_odd_faithful_nonFF_of_parity_sources
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hodd : Odd n)
    (hseed : OddSeedSource T L H n)
    (hlower : DisplacementSource T L H n) :
    ∃ A B : Subgroup G, CartanPair T L H A B ∧
      ∃ s : Seed T L H A n,
        let E := setup T L s.V H A
        let := point_normal_in_span s.f8
        let := ChapterF.Section08.Setup.lemma_F_8_5_two s.f8
        ∃ (ρ : Representation (ZMod 2) E.HStar
            (Additive (E.U ⧸ E.V₁.subgroupOf E.U)))
          (_c : Representation.BinaryConjugationSection E.H E.U E.V₁
            (ρ.comp (QuotientGroup.mk' (pCore 2 E.H)))),
          Function.Injective ρ ∧ ¬ Representation.BinaryOffender.IsFFModule ρ := by
  obtain ⟨A, B, c⟩ := D.rankOne_exists_cartanPair h.toHypothesis1221 hn hpsl hH hgen
  obtain ⟨s⟩ := hseed A B c hodd
  let := point_normal_in_span s.f8
  let := ChapterF.Section08.Setup.lemma_F_8_5_two s.f8
  obtain ⟨ρ, d, hρ, _⟩ := exists_faithful_action s.f8
  exact ⟨A, B, c, s, ρ, d, hρ,
    not_ff_of_large_displacement s.f8 s.quotient_rank (hlower A B c hodd s) ρ d⟩

/-- Conditional assembly of the three genuine source obligations. This
does not discharge the odd setup, displacement or critical-pair theorem. -/
theorem rankOne_even_exponent_of_parity_sources
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hseed : OddSeedSource T L H n)
    (hlower : DisplacementSource T L H n)
    (hcritical : CriticalSource T L H n) : Even n := by
  obtain ⟨A, B, c⟩ := D.rankOne_exists_cartanPair h.toHypothesis1221 hn hpsl hH hgen
  rcases Nat.even_or_odd n with heven | hodd
  · exact heven
  · obtain ⟨s⟩ := hseed A B c hodd
    have hlarge := hlower A B c hodd s
    obtain ⟨y, hy, hy2, hyQ, hsmall⟩ := hcritical A B c hodd s hlarge
    have hbig := hlarge y hy hy2 hyQ
    omega

/-- The field-four/Borel consumer can use the three parity sources without
an additional evenness premise. Its other source branches remain explicit. -/
theorem field_four_and_borel_of_parity_and_cubic_sources
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hseed : OddSeedSource T L H n)
    (hlower : DisplacementSource T L H n)
    (hcritical : CriticalSource T L H n)
    (hright : ∀ A B : Subgroup G, CartanPair T L H A B → Nat.card B = 3)
    (hinside : ∀ A B C : Subgroup G, LinearFieldCartan T L H A B C n →
      C ≤ normalizer (residual H : Set G) → n = 2 ∧ C = B)
    (houtside : ∀ A B C : Subgroup G, LinearFieldCartan T L H A B C n →
      ¬ C ≤ normalizer (residual H : Set G) → False) :
    n = 2 ∧ localBorel T L ≤ omegaCentralizer T :=
  D.field_four_and_borel_of_linear_cubic_sources h.toHypothesis1221 hn hpsl
    hH hgen hK hnf
    (D.rankOne_even_exponent_of_parity_sources h hn hpsl hH hgen hseed hlower hcritical)
    hright hinside houtside

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
