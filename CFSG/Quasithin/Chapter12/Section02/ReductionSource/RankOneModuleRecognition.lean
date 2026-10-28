module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModulePreparation
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionGeneration
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionEquality

/-!
# The small-generation recognition assembly on the original reduced subgroup

The numeric bound at most one supplies the exact generation hypothesis of
6.1.1, because each actual H* member has positive attained generation.
Together with the existing preparation this constructs every source input
on R₂(LT), with commutator layer [R₂(LT),L].

The final implication below deliberately retains two earlier proof inputs:
the natural reduction 6.1.27 and the subsequent identification under that
reduction. They can be proved independently. The latter must construct
the compatible quotient and extraspecial geometry in the equality branch
and exclude the strict-intersection branch. The equality branch's global
recognition is proved in `RankOneModuleRecognitionEquality`.

This conditional assembly is not the unconditional `SmallExit` theorem.
Its two source inputs remain with the recognition assembly owner.

Source: Aschbacher--Smith, 6.1.1, 6.1.27, 6.2.19 and 12.2.2(3d),
printed pp.663, 679, 690--691 and 795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual small-generation branch satisfies all of Hypothesis 6.1.1.
In particular its equality clause is proved, rather than inferred from a
bare infimum definition. -/
theorem hypothesis611_of_generation_le_one (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hsmall : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      ChapterE.generationParameter H ≤ 1)
    (hmodel : ¬ Chapter6.Source.IsOneOrTwoA5Modules L (commutatorLayer T L)) :
    Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n := by
  exact hypothesis611 D h hn hpsl
    (Chapter6.Source.RankOneRecognition.hstar_generation_one h.simpleQTKE hsmall) hmodel

/-- Apply the equality-branch identification to the literal whole reduced
subgroup used by Chapter 12. The quotient, core and cubic element are all
marked in the original ambient group. Their construction remains the
earlier source geometry obligation. -/
theorem m22_of_reduced_source_geometry
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hsmall : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      ChapterE.generationParameter H ≤ 1)
    (hmodel : ¬ Chapter6.Source.IsOneOrTwoA5Modules L (commutatorLayer T L))
    (hnatural : Chapter6.Source.Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (H : Subgroup G) (z : G) (hH : H = centralizer ({z} : Set G))
    (hTH : (T : Subgroup G) ≤ H)
    [((commutatorLayer T L).subgroupOf (normalizer (L : Set G))).Normal]
    (hq : Chapter6.M22Recognition.CentralizerExtension.CompatibleSymmetricFiveQuotient
      ((commutatorLayer T L).subgroupOf (normalizer (L : Set G)))
      (L.subgroupOf (normalizer (L : Set G))))
    (P : Subgroup H) [P.Normal]
    (hP : Chapter6.M22Recognition.CentralizerExtension.CoreData P)
    (ha : Chapter6.M22Recognition.CentralizerExtension.NaturalFourOrbit P
      ((Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)).subgroupOf H))
    (hZS : Chapter6.M22Recognition.CentralizerExtension.coreCenter P ≤
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)).subgroupOf H)
    (hSP : (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)).subgroupOf H ≤ P)
    (hPT : P.map H.subtype ≤ (T : Subgroup G))
    (hbranch : (Chapter6.M22Recognition.CentralizerExtension.sourceEight
      ((Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)).subgroupOf H)).map H.subtype ⊓
        commutatorLayer T L = Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L))
    (d : G) (hdL : d ∈ L)
    (hdT : d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G)) (hd : orderOf d = 3) :
    Nonempty (G ≃* Sporadic.Mathieu.M22) := by
  exact Chapter6.Source.RankOneRecognition.m22_of_source_geometry
    (hypothesis611_of_generation_le_one D h hn hpsl hsmall hmodel)
    hnatural H z hH hTH hq P hP ha hZS hSP hPT hbranch d hdL hdT hd

/-- Assemble the exact specialized exit once both independent earlier source
implications have been proved. These inputs are not assertions of their
unconditional source theorems. -/
theorem smallExit_of_source_reduction_and_recognition_of_many
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hnatural : Chapter3.HasMaximalOutside T (normalizer (L : Set G)) →
      Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
        (normalizer (L : Set G)) (wholeReduced T L) n →
      Chapter6.Source.Conclusion6127 (T : Subgroup G) L
        (normalizer (L : Set G)) (wholeReduced T L) n)
    (hrecognition : Chapter3.HasMaximalOutside T (normalizer (L : Set G)) →
      Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
        (normalizer (L : Set G)) (wholeReduced T L) n →
      Chapter6.Source.Conclusion6127 (T : Subgroup G) L
        (normalizer (L : Set G)) (wholeReduced T L) n →
      Nonempty (G ≃* Sporadic.Mathieu.M22)) : SmallExit T L := by
  intro _ hsmall hmodel
  have hout := D.rankOne_hasMaximalOutside_of_many h.toHypothesis1221 hmany
  have h611 := hypothesis611_of_generation_le_one D h.toHypothesis1221 hn hpsl hsmall hmodel
  exact hrecognition hout h611 (hnatural hout h611)

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
