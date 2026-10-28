module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldCartan
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearField
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLocalCartan

/-!+# Constructing the compatible cubic on the original chosen setup

The genuine Hall construction chooses A and B inside the original local
Borel and outside intersection. The PSL₂ quotient supplies cyclicity and
the exact order of A; evenness then constructs C≤A of order three.
Thus the conditional source assembly no longer assumes a preselected
`LinearFieldCartan` witness.

Four source inputs remain explicit: parity (5.1.17), the right Hall order
(5.1.10), the normalizing cubic branch (5.1.18--20), and exclusion of the
escaping cubic (5.1.21--23 and the final contradiction). In particular,
5.1.18 supplies C=B, whereas n=2 requires the subsequent argument. These
are conditional consumers, not unconditional assertions of 5.1.14.
Source: Aschbacher--Smith, printed pp.634--635,638--646; 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- Construct all three literal Cartans from parity and the right Hall order.
The latter is quantified over the compatible pairs which Hall existence selects. -/
theorem rankOne_exists_linearFieldCartan_of_even
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (heven : Even n)
    (hright : ∀ A B : Subgroup G, CartanPair T L H A B → Nat.card B = 3) :
    ∃ A B C : Subgroup G, LinearFieldCartan T L H A B C n := by
  obtain ⟨A, B, c⟩ := D.rankOne_exists_cartanPair h hn hpsl hH hgen
  obtain ⟨C, hc⟩ := c.exists_linearFieldCartan_of_even D.sylow_normalizes_component
    hpsl heven (hright A B c)
  exact ⟨A, B, C, hc⟩

/-- Literal numerical/Borel assembly with the source branches kept separate.
There is no assumed Cartan witness or assumed full equality A=B. -/
theorem field_four_and_borel_of_linear_cubic_sources
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (heven : Even n)
    (hright : ∀ A B : Subgroup G, CartanPair T L H A B → Nat.card B = 3)
    (hinside : ∀ A B C : Subgroup G, LinearFieldCartan T L H A B C n →
      C ≤ normalizer (residual H : Set G) → n = 2 ∧ C = B)
    (houtside : ∀ A B C : Subgroup G, LinearFieldCartan T L H A B C n →
      ¬ C ≤ normalizer (residual H : Set G) → False) :
    n = 2 ∧ localBorel T L ≤ omegaCentralizer T := by
  obtain ⟨A, B, C, c⟩ := D.rankOne_exists_linearFieldCartan_of_even
    h hn hpsl hH hgen heven hright
  apply D.field_four_and_borel_of_linear_cubic_branches h hH hK hnf c
  · intro hCN
    obtain ⟨hn2, hCB⟩ := hinside A B C c hCN
    exact c.left_eq_right_of_cubic_eq hn2 hCB
  · exact houtside A B C c

/-- The chosen-module consumer receives both required numerical/Borel inputs
from the actual Cartans; chosen T-invariance retains its independent producer. -/
theorem a5_model_of_linear_cubic_sources
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (heven : Even n)
    (hright : ∀ A B : Subgroup G, CartanPair T L H A B → Nat.card B = 3)
    (hinside : ∀ A B C : Subgroup G, LinearFieldCartan T L H A B C n →
      C ≤ normalizer (residual H : Set G) → n = 2 ∧ C = B)
    (houtside : ∀ A B C : Subgroup G, LinearFieldCartan T L H A B C n →
      ¬ C ≤ normalizer (residual H : Set G) → False) :
    Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  obtain ⟨hn2, hB⟩ := D.field_four_and_borel_of_linear_cubic_sources
    h hn hpsl hH hgen hK hnf heven hright hinside houtside
  exact D.a5_model_of_linear_source_borel h hH hK hnf hpsl hn2 hTV hB

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
