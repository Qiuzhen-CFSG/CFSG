module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.BinaryKnownSimple
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.SmallCovers
/-!
# Restricted containing catalogue for the smaller SL2(5)

The full known-simple A.3.6 catalogue is inspected on the actual containing
component. Full-Sylow nonenlargement handles the classical characteristic-two
rows. The intrinsic even-characteristic kernel criterion excludes twisted
and sporadic rows; central involutions and odd-center transport exclude the
small remaining carriers. Only signed odd-prime degree-three models remain.
Their prime parameter is identified by the subsequent Levi argument.
Source: Aschbacher–Smith A.3.12 and C.5.12, pp.47–48,163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02 Chapter1.Section02.LocalModels ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

theorem sl2_five_larger_selection_knownSimple
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents T) (hL : L.IsCComponent)
    (hBL : B ≤ L) [IsQuasisimple B] [IsQuasisimple L]
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) (hmodel : IsSL B 2 5) :
    B=L ∨ ∃ p, p.Prime ∧ Odd p ∧ ∃ u,
      IsPSLSign L u 3 p ∨ IsSLSign L u 3 p := by
  have hmodels := quasisimple_containing_component_models_knownSimple hG hO hL
  have heven (he : IsEvenCharacteristic L) : False :=
    not_sl2_five_containing_even T hB hL hBL hTB he hmodel
  rcases hmodels with ⟨_,hs⟩ | ⟨_,hs⟩
  · cases hs with
    | alternating d hd hm =>
        have hd' : d=5 ∨ d=6 ∨ d=7 ∨ d=8 := by omega
        rcases hd' with rfl | rfl | rfl | rfl
        · exact .inl (eq_of_small_alternating_containing_component T hB hL hBL (.inl hm))
        · exact .inl (eq_of_small_alternating_containing_component T hB hL hBL (.inr (.inl hm)))
        · obtain ⟨e⟩ := hm
          exact (no_sl2_five_injective_alternating_seven hmodel
            (e.toMonoidHom.comp (inclusion hBL)) (e.injective.comp (inclusion_injective hBL))).elim
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
          obtain ⟨_,hb⟩ := proper_primePSL2_models T hB hL hBL heq hp ho hm'
          exact (sl2_five_not_alternating hmodel 5 (.inl rfl) hb).elim
        · obtain ⟨_,hb⟩ := proper_quadraticPSL2_models T hB hL hBL heq hp ho hm
          exact (sl2_five_not_psl2 hmodel p hb).elim
    | three_odd p hp ho u hm => exact .inr ⟨p,hp,ho,u,.inl hm⟩
    | rank_one hm => exact .inl (eq_of_bender_containing_component T hB hL hBL hm)
    | rank_two hm =>
        cases hm with
        | linear m hm he => exact .inl (eq_of_binary_linear_three_model T hB hL hBL hm he)
        | symplectic m hm he => exact .inl (eq_of_binary_symplectic_model T hB hL hBL hm he)
        | g2 _ _ he => exact .inl (eq_of_binary_g2_model T hB hL hBL he)
        | triality m hm he =>
            exact (heven (MainConverse.TrialityLocal.quasithin_and_evenCharacteristic_of_isTrialityGroupAt m hm he).2).elim
        | ree m hm he =>
            obtain ⟨d,⟨e⟩⟩ := he
            exact (heven (MainConverse.ReeLocal.quasithin_evenCharacteristic_of_iso hm (e.trans d.modelEquiv)).2).elim
        | symplectic_derived he => exact .inl (eq_of_binary_symplectic_derived_model T hB hL hBL he)
        | g2_derived he => exact .inl (eq_of_binary_g2_derived_model T hB hL hBL he)
        | tits he => exact .inl (eq_of_tits_model T hB hL hBL he)
    | binary_linear d hd hm => exact .inl (eq_of_binary_linear_four_or_five T hB hL hBL hd hm)
    | sporadic name _ hm =>
        obtain ⟨e⟩ := hm
        exact (heven (sporadic_evenCharacteristic name e)).elim
    | janko_one hm =>
        obtain ⟨e⟩ := hm
        exact (no_sl2_five_injective_janko_one hmodel
          (e.toMonoidHom.comp (inclusion hBL)) (e.injective.comp (inclusion_injective hBL))).elim
  · cases hs with
    | classical u q hq hm =>
        rcases hq with ⟨m,hm,rfl,_⟩ | ⟨hp,ho⟩
        · cases u with
          | false => exact .inl (eq_of_binary_special_linear_three_model T hB hL hBL (by omega) hm)
          | true => exact .inl (eq_of_binary_su3_containing_component T hB hL hBL (by omega) hm)
        · exact .inr ⟨q,hp,ho,u,.inr hm⟩
    | alternating_six hm => exact .inl (eq_of_small_alternating_containing_component T hB hL hBL (.inr (.inr hm)))
    | alternating_seven hm =>
        exact (no_sl2_five_injective_three_alternating_seven hmodel hm (inclusion hBL) (inclusion_injective hBL)).elim
    | mathieu hm => exact (not_sl2_five_containing_m22_cover T hB hL hBL hTB hmodel hm).elim
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
