module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.SeedSylow
public import CFSG.Quasithin.Chapter3.Section01.CommonNormalSource
public import Theory.GroupTheory.PGroup.CharacteristicKernel
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The original A₅ seed normalizer

The actual local core is Sylow in the full seed centralizer. If that
centralizer escapes M=N(L), choose a minimal overgroup H of T outside M
inside C(V₃)T. Its two-residual lies in C(V₃), so the same core is Sylow
in O²(H)R. The genuine common-normal theorem 3.1.1 produces a nontrivial
subgroup of R normal in ⟨LT,H⟩. Uniqueness over LT traps its normalizer
in M, contradicting the choice of H. Frattini then controls N(V₃).

The full earlier A.3.12 embedding theorem remains explicit, exactly as
in the proved source 3.1.1 interface; no centralizer or normalizer
conclusion is assumed. Source: Aschbacher–Smith 13.2.3(2), p.879.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
include d hA312

/-- The common-normal argument localizes the entire seed centralizer. -/
theorem seed_centralizer : centralizer (V₃ : Set G) ≤ normalizer (L : Set G) := by
  classical
  by_contra hout
  let C := centralizer (V₃ : Set G)
  let J := C ⊔ (T : Subgroup G)
  let R := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hVT : V₃ ≤ (T : Subgroup G) := d.third_le.trans d.chosen.le_sylow
  have hJN : J ≤ normalizer (V₃ : Set G) :=
    sup_le (Subgroup.centralizer_le_normalizer _) d.third_invariant
  have hVcore : V₃ ≤ J.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le hVT) (hVT.trans le_sup_right) hJN
  have hJ : J ∈ Chapter1.HOver G (T : Set G) := by
    refine ⟨?_,show (T : Subgroup G) ≤ J from le_sup_right⟩
    intro he
    exact d.third_ne_bot (bot_unique (hVcore.trans_eq he))
  obtain ⟨H,hHJ,hH⟩ := exists_minimal_le_of_wellFoundedLT
    (fun Y : Subgroup G => Y ∈ Chapter1.HOver G (T : Set G) ∧
      ¬ Y ≤ normalizer (L : Set G)) J ⟨hJ,fun h => hout (le_sup_left.trans h)⟩
  have hstar : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) := hH
  have hNC : J ≤ normalizer (C : Set G) :=
    hJN.trans (normalizer_le_normalizer_centralizer V₃)
  let : (C.subgroupOf J).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hNC
  have hquot : IsPGroup 2 (J ⧸ C.subgroupOf J) := by
    apply quotient_isPGroup_of_sup_eq_top ((T : Subgroup G).subgroupOf J) (C.subgroupOf J)
      (T.isPGroup'.comap_subtype)
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_right,
      map_subgroupOf_eq_of_le le_sup_left,← MonoidHom.range_eq_map,range_subtype]
    exact sup_comm _ _
  have hresJ : (pResidual 2 J).map J.subtype ≤ C := by
    have hr : pResidual 2 J ≤ C.subgroupOf J := sInf_le ⟨inferInstance,hquot⟩
    exact (map_mono hr).trans_eq (map_subgroupOf_eq_of_le le_sup_left)
  have hresH : (pResidual 2 H).map H.subtype ≤ C :=
    (embedded_pResidual_mono 2 hHJ).trans hresJ
  have hs : Chapter1.IsSylowIn 2 R ((pResidual 2 H).map H.subtype ⊔ R) := by
    have hc : Chapter1.IsSylowIn 2 R C := d.core_seed_sylow
    obtain ⟨hp,hle,hmax⟩ := Chapter1.isSylowIn_iff.mp hc
    exact Chapter1.isSylowIn_iff.mpr
      ⟨hp,le_sup_right,fun U hu hRU hU => hmax U hu hRU (hU.trans (sup_le hresH hle))⟩
  have hLT : L ⊔ (T : Subgroup G) ∈ Chapter1.HOver G (T : Set G) :=
    ⟨d.core_ne_bot,show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right⟩
  have hnR : L ⊔ (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  obtain ⟨N,hNR,hne,hn⟩ := Chapter3.source_common_normal_of_A312
    d.hypothesis.qtke hA312 T (L ⊔ (T : Subgroup G)) H R hLT hH.1.1
    (Chapter3.HStar.hasUniqueMaximalOver T d.normalizes_L hstar)
    d.core_ne_bot d.core_le_sylow hs hnR
  have hnorm := (Chapter3.normalIn_iff_le_normalizer.mp hn).2
  have hNM : normalizer (N : Set G) ≤ normalizer (L : Set G) :=
    normalizer_le_of_unique_maximalTwoLocal d.unique_maximal_overgroup
      ((isPGroup_pCoreIn 2 _).to_le hNR) hne
      (Chapter3.le_generated_left.trans hnorm)
  exact hH.1.2 (Chapter3.le_generated_right.trans (hnorm.trans hNM))

/-- Original 13.2.3(2), on the marked third subgroup of the same Context. -/
theorem seed_normalizer : normalizer (V₃ : Set G) ≤ normalizer (V : Set G) :=
  d.seed_normalizer_of_centralizer (d.seed_centralizer hA312)

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
