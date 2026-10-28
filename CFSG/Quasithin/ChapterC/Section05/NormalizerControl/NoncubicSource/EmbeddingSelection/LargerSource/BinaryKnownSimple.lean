module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuasisimpleContaining
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Bender
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryLinear
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SmallAlternating
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.PrimePSL2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuadraticPSL2
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.EvenContaining
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.OddThree
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.RankTwo
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.RankTwo.SpecialLinear
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SurvivingParameters
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
/-!
# Complete binary smaller-component selection over known simple groups

The actual containing component has its full A.3.6 catalogue. Full-Sylow
nonenlargement handles the even classical and small alternating carriers;
intrinsic Sylow faithfulness excludes the remaining characteristic-two
carriers. The odd ternary exclusion uses involution centralizers. Dickson's
prime and quadratic PSL2 lists and elementary two-ranks give precisely the
five surviving models and field degree two.

The input is the original local component and its normalized full Sylow,
with no embedding-list or faithful-action premise.
Source: Aschbacher–Smith A.3.12 and C.5.12–13, printed pp.47–48,162–163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02 Chapter1.Section02.LocalModels ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

theorem binary_larger_selection_knownSimple
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents T) (hL : L.IsCComponent)
    (hBL : B ≤ L) [IsQuasisimple B]
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    {n : ℕ} (hn : 1 < n) (hmodel : ClassicalGroup.IsPSL B 2 (2^n)) :
    B = L ∨ n = 2 ∧
      (IsAlternating L 7 ∨ IsAlternatingCover L 7 ∨ Nonempty (L ≃* Janko1.Model) ∨
        ClassicalGroup.IsPSL L 2 25 ∨
        ∃ p, A312ExceptionalPrime p ∧ ClassicalGroup.IsPSL L 2 p) := by
  obtain ⟨hq,hmodels⟩ := binary_containing_component_models_knownSimple hG hO hL hBL hn hmodel
  let : IsQuasisimple L := hq
  have hev := binary_containing_even_exclusions T hB hL hBL hTB hn hmodel
  have hfinite (hm : IsAlternating L 7 ∨ IsAlternatingCover L 7 ∨ Nonempty (L ≃* Janko1.Model)) :
      B = L ∨ n = 2 ∧
        (IsAlternating L 7 ∨ IsAlternatingCover L 7 ∨ Nonempty (L ≃* Janko1.Model) ∨
          ClassicalGroup.IsPSL L 2 25 ∨
          ∃ p, A312ExceptionalPrime p ∧ ClassicalGroup.IsPSL L 2 p) := by
    refine .inr ⟨binary_parameter_of_surviving_containing_model B L hBL hn hmodel hm,?_⟩
    rcases hm with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
  rcases hmodels with ⟨_,hs⟩ | ⟨_,hs⟩
  · cases hs with
    | alternating d hd hm =>
        have hd' : d=5 ∨ d=6 ∨ d=7 ∨ d=8 := by omega
        rcases hd' with rfl | rfl | rfl | rfl
        · exact .inl (eq_of_small_alternating_containing_component T hB hL hBL (.inl hm))
        · exact .inl (eq_of_small_alternating_containing_component T hB hL hBL (.inr (.inl hm)))
        · exact hfinite (.inl hm)
        · apply Or.inl
          apply eq_of_binary_linear_four_or_five T hB hL hBL (.inl rfl)
          obtain ⟨e⟩ := hm
          exact ⟨ZMod 2,inferInstance,inferInstance,by simp,
            ⟨e.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm⟩⟩
    | linear_odd p e hp ho he _ hm =>
        by_cases heq : B=L
        · exact .inl heq
        rcases he with rfl | rfl
        · have hm' : ClassicalGroup.IsPSL L 2 p := by simpa only [pow_one] using hm
          obtain ⟨hp',hb⟩ := proper_primePSL2_models T hB hL hBL heq hp ho hm'
          exact .inr ⟨binary_parameter_of_alternating_five (by omega) hmodel hb,
            .inr (.inr (.inr (.inr ⟨p,hp',hm'⟩)))⟩
        · obtain ⟨hlarge,hb⟩ := proper_quadraticPSL2_models T hB hL hBL heq hp ho hm
          obtain ⟨hn2,rfl⟩ := binary_odd_prime_parameters hn hmodel hp ho hlarge hb
          exact .inr ⟨hn2,.inr (.inr (.inr (.inl (by simpa using hm))))⟩
    | three_odd p hp ho u hm =>
        exact ((not_odd_three_binary_containing T B L hBL hL.subnormal hn hmodel hTB hp ho u).1 hm).elim
    | rank_one hm => exact .inl (eq_of_bender_containing_component T hB hL hBL hm)
    | rank_two hm =>
        cases hm with
        | linear m hm he => exact .inl (eq_of_binary_linear_three_model T hB hL hBL hm he)
        | symplectic m hm he => exact .inl (eq_of_binary_symplectic_model T hB hL hBL hm he)
        | g2 _ _ he => exact .inl (eq_of_binary_g2_model T hB hL hBL he)
        | triality m hm he => exact (hev.1 m hm he).elim
        | ree m hm he => exact (hev.2.1 m hm he).elim
        | symplectic_derived he => exact .inl (eq_of_binary_symplectic_derived_model T hB hL hBL he)
        | g2_derived he => exact .inl (eq_of_binary_g2_derived_model T hB hL hBL he)
        | tits he => exact .inl (eq_of_tits_model T hB hL hBL he)
    | binary_linear d hd hm => exact .inl (eq_of_binary_linear_four_or_five T hB hL hBL hd hm)
    | sporadic name hne hm => exact (hev.2.2.1 name hne hm).elim
    | janko_one hm => exact hfinite (.inr (.inr hm))
  · cases hs with
    | classical u q hq hm =>
        rcases hq with ⟨m,hm,rfl,_⟩ | ⟨hp,ho⟩
        · cases u with
          | false => exact .inl (eq_of_binary_special_linear_three_model T hB hL hBL (by omega) hm)
          | true => exact .inl (eq_of_binary_su3_containing_component T hB hL hBL (by omega) hm)
        · exact ((not_odd_three_binary_containing T B L hBL hL.subnormal hn hmodel hTB hp ho u).2 hm).elim
    | alternating_six hm => exact .inl (eq_of_small_alternating_containing_component T hB hL hBL (.inr (.inr hm)))
    | alternating_seven hm => exact hfinite (.inr (.inl hm))
    | mathieu hm => exact (hev.2.2.2 hm).elim
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
