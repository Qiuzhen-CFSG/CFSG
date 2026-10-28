module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldRightCartan
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldCartan
/-!
# Discharging the right Cartan order on the original chosen setup

The literal PSL₃(4) residual quotient supplies the order of every compatible
right Hall subgroup. This discharges `hright` in both the Cartan construction
and the field-four/Borel consumer. Parity, residual local membership and
nonfaithfulness, and the two cubic branches remain their independent source
inputs; the final field-four/Borel assembly belongs to their common owner.

Source: Aschbacher--Smith, Notation 5.1.9, 5.1.10, and the opening of
5.1.14, printed pp.634,638; the Chapter 12 application is on p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- The actual right Cartan in the chosen setup has order three. -/
theorem rankOne_right_cartan_card_of_linear_residual
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) : Nat.card B = 3 :=
  c.right_card_of_linear_residual D.sylow_normalizes_component hH hgen hm

/-- The source PSL₃(4) quotient discharges the right-order input to the literal
Cartan construction. Only the independently proved parity remains. -/
theorem rankOne_exists_linearFieldCartan_of_even_of_linear_residual
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (heven : Even n) :
    ∃ A B C : Subgroup G, LinearFieldCartan T L H A B C n :=
  D.rankOne_exists_linearFieldCartan_of_even h hn hpsl hH hgen heven
    (fun _ _ c => D.rankOne_right_cartan_card_of_linear_residual hH hgen hm c)

/-- Literal field-four/Borel assembly with the right Hall order discharged.
Parity and both cubic branches retain their independent source producers. -/
theorem field_four_and_borel_of_linear_cubic_sources_of_linear_residual
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (heven : Even n)
    (hinside : ∀ A B C : Subgroup G, LinearFieldCartan T L H A B C n →
      C ≤ normalizer (residual H : Set G) → n = 2 ∧ C = B)
    (houtside : ∀ A B C : Subgroup G, LinearFieldCartan T L H A B C n →
      ¬ C ≤ normalizer (residual H : Set G) → False) :
    n = 2 ∧ localBorel T L ≤ omegaCentralizer T :=
  D.field_four_and_borel_of_linear_cubic_sources h hn hpsl hH hgen hK hnf heven
    (fun _ _ c => D.rankOne_right_cartan_card_of_linear_residual hH hgen hm c)
    hinside houtside

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
