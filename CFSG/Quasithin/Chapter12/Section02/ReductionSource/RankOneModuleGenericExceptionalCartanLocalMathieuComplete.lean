module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalMathieuComplete
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocalRecognition

/-!
# The complete selected M₂₃ escape for the original chosen module

The source's solvable Cartan--Sylow join now proves the original Mathieu
quotient action is a three-group. Thus the same selected component supplies
its inverted escaping cubic and the full local witness without any extra
action premise. Apply the original whole-module conclusion and the chosen
module marking at the original field degree.

Exhaustive selection of the component, the nonquasisimple reduction and
binary-triality exclusion remain obligations of the full local source theorem.
Source: Aschbacher--Smith 5.1.13 and 12.2.2, printed pp.636--638,795,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y : Subgroup G}
  (a : ChosenModule T L V)
include a

/-- The actual selected M₂₃ component and original inverted cubic witness. -/
theorem rankOne_local_cartan_mathieu_twentyThree_witness
    {K : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M23)) :
    ∃ D : Subgroup G, LocalCartanWitness T H A Y (C.map Y.subtype) D := by
  exact LocalSieve.mathieu_twentyThree_local_witness
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hKT hKL horbit hY hescape C hC hKC hm

/-- Full original whole-module and chosen-module conclusions in the M₂₃ row. -/
theorem rankOne_local_cartan_mathieu_twentyThree_exceptional
    {K : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) [C.Normal]
    (hKC : K ≤ C.map Y.subtype)
    (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M23)) :
    CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H ∧
      RankOneModule.ExceptionalExit T L H ∧ n = 2 ∧
      IsConjugationModel L V a5Module := by
  have hi := a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  obtain ⟨_,he⟩ := LocalSieve.mathieu_twentyThree_cartan_exceptional hi
    hH hgen c hKT hKL horbit hY hescape C hC hKC hm
  have hex := RankOneModule.exceptional_of_cartan_conclusion he
  exact ⟨he,hex,a.rankOne_exceptional_module_and_exponent hn hpsl hex⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
