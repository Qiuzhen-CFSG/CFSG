module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.CriticalPairProper
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParity

/-!
# Parity after the two terminal critical-pair cases

The F.8 critical-pair implication is now proved on the literal selected module.
Apply it to the compatible Cartans from the original chosen-module setup. The
only parity premises left here are the odd-exponent preparation and the
nine-dimensional displacement theorem. Their construction, and thus the
unconditional 5.1.17 theorem, remain with qt-d-1222-linear-field-parity.

The second application supplies this parity result to the field-four/Borel
consumer without an additional critical-pair premise. Its independent cubic
source inputs remain with qt-d-1222-linear-field-four-borel.
Source: Aschbacher–Smith, 5.1.17, printed pp.640–642, and its application in
12.2.2, printed p.795 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- Parity on the original chosen setup, with the terminal source discharged. -/
theorem rankOne_even_exponent_of_seed_and_displacement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hseed : OddSeedSource T L H n)
    (hlower : DisplacementSource T L H n) : Even n :=
  D.rankOne_even_exponent_of_parity_sources h hn hpsl hH hgen hseed hlower
    (criticalSource T L H n)

/-- The field-four/Borel application with both critical-pair cases proved. -/
theorem field_four_and_borel_of_seed_displacement_and_cubic_sources
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hseed : OddSeedSource T L H n)
    (hlower : DisplacementSource T L H n)
    (hright : ∀ A B : Subgroup G, CartanPair T L H A B → Nat.card B = 3)
    (hinside : ∀ A B C : Subgroup G, LinearFieldCartan T L H A B C n →
      C ≤ normalizer (residual H : Set G) → n = 2 ∧ C = B)
    (houtside : ∀ A B C : Subgroup G, LinearFieldCartan T L H A B C n →
      ¬ C ≤ normalizer (residual H : Set G) → False) :
    n = 2 ∧ localBorel T L ≤ omegaCentralizer T :=
  D.field_four_and_borel_of_parity_and_cubic_sources h hn hpsl hH hgen hK hnf
    hseed hlower (criticalSource T L H n) hright hinside houtside

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
