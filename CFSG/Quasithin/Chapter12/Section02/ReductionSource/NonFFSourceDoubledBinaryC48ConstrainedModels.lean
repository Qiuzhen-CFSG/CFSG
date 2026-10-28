module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedLocals
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedBinaryThree
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedSeven
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedLinearTwo

/-!
# Four remaining star models for the original constrained witness

The complete B.5 source classifier, applied to the literal star module,
retains only G2(2)', A7, A8 and SL5(2) after the proved original local and
order exclusions. This is a model sieve; it does not identify the original
residual with a parabolic residual or supply its final module marking.
Source: Aschbacher--Smith C.2.7 and C.4.5--8, pp.145--154.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Chapter4.Section04.NormalizedRankOneOddControl
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original constrained star component has one of four finite models. -/
theorem sourceOrbit_binary_witness_constrained_four_models
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    let C := starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype)
    Nonempty (C ≃* commutator (Atlas.G2.Model (ZMod 2))) ∨
      Nonempty (C ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (C ≃* alternatingGroup (Fin 8)) ∨
      Nonempty (C ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) := by
  dsimp only
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  have hi := hc.constrained_source_input K hK hq hout hfK
  cases ChapterC.C27Source.star_model_from_source hi with
  | linearTwo E e =>
    exact (hc.no_constrained_component_star_linear_two K hK hq hout hfK E e).elim
  | linearThree E e =>
    by_cases hE : E.degree = 1
    · exact (D.sourceOrbit_binary_witness_constrained_not_binary_three
        h hd F hF hmodel hw hWJ hJC K hK hq hout hfK E hE ⟨e⟩).elim
    · exact (D.sourceOrbit_binary_witness_constrained_not_linear_three_large
        h hd F hF hmodel hw hWJ hJC K hK hq hout hfK E
        (by have := E.degree_pos; omega) ⟨e⟩).elim
  | symplectic E hE e =>
    exact (D.sourceOrbit_binary_witness_constrained_not_sp4
      h hd F hF hmodel hw hWJ hJC K hK hq hout hfK E hE ⟨e⟩).elim
  | g2 E hE e =>
    exact (D.sourceOrbit_binary_witness_constrained_not_g2
      h hd F hF hmodel hw hWJ hJC K hK hq hout hfK E hE ⟨e⟩).elim
  | g2DerivedTwo e => exact Or.inl ⟨e⟩
  | alternating n hn e =>
    rcases hn with rfl | rfl | rfl | rfl
    · exact (D.sourceOrbit_binary_witness_constrained_not_small_alternating
        h hd F hF hmodel hw hWJ hJC K hK hq hout hfK 5 (Or.inl rfl) ⟨e⟩).elim
    · exact (D.sourceOrbit_binary_witness_constrained_not_small_alternating
        h hd F hF hmodel hw hWJ hJC K hK hq hout hfK 6 (Or.inr rfl) ⟨e⟩).elim
    · exact Or.inr (Or.inl ⟨e⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨e⟩))
  | linearFiveTwo e => exact Or.inr (Or.inr (Or.inr ⟨e⟩))
  | tripleSix ec eq =>
    exact (D.sourceOrbit_binary_witness_constrained_not_triple_six
      h hd F hF hmodel hw hWJ hJC K hK hq hout hfK ⟨⟨ec⟩,⟨eq⟩⟩).elim

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
