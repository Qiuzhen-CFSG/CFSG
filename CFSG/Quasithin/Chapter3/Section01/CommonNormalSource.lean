module
public import CFSG.Quasithin.ChapterC.Section05.CommonNormalSource.KnownSimple
public import CFSG.Quasithin.Chapter3.Section01.ResidualSylow
public import CFSG.Quasithin.Chapter1.Section01Overgroups
/-!
# The original common-normal theorem for simple QTKE groups

Membership in H(T) gives characteristic two by 1.1.4(6). Unique maximality
restricts to the literal Sylow subgroup of H, and the supplied residual
Sylow witness is unchanged. The completed C.5.8 theorem then produces the
nontrivial subgroup of R normal in the actual join. The independent full
A.3.12 embedding implication remains explicit.

Source: Aschbacher–Smith Theorem 3.1.1, printed pp.571–572.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter3
universe u
variable {G : Type u} [Group G] [Finite G]
private theorem unique_maximal_subgroupOf {S H : Subgroup G}
    (hu : Order.HasUniqueMaximalOver S H) :
    Order.HasUniqueMaximalOver (S.subgroupOf H) ⊤ := by
  obtain ⟨B,hSB,hBH⟩ := hu.2.exists
  have hm : (B.subgroupOf H).map H.subtype = B := map_subgroupOf_eq_of_le hBH.le
  have ht : (⊤ : Subgroup H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map,range_subtype]
  have hc : IsCoatom (B.subgroupOf H) := by
    refine ⟨?_,?_⟩
    · intro he
      exact hBH.ne (hm.symm.trans ((congrArg (map H.subtype) he).trans ht))
    · intro Y hBY
      have hh : B < Y.map H.subtype := by
        rw [← hm]
        exact (map_lt_map_iff_of_injective H.subtype_injective).mpr hBY
      have he := (hBH.eq_or_eq hh.le (map_subtype_le Y)).resolve_left hh.ne'
      exact map_injective H.subtype_injective (he.trans ht.symm)
  have hle : S.subgroupOf H ≤ B.subgroupOf H := subgroupOf_mono H hSB
  refine ⟨hle.trans_lt hc.lt_top,B.subgroupOf H,⟨hle,hc.covBy_top⟩,?_⟩
  intro Y hY
  have hSY : S ≤ Y.map H.subtype := by
    rw [← map_subgroupOf_eq_of_le hu.1.le]
    exact map_mono hY.1
  have hYH : Y.map H.subtype < H := by
    simpa only [ht] using
      (map_lt_map_iff_of_injective H.subtype_injective).mpr hY.2.lt
  have hYB : Y ≤ B.subgroupOf H := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [hm]
    exact hu.le_maximal ⟨hSB,hBH⟩ hSY hYH
  exact ((hY.2.eq_or_eq hYB le_top).resolve_right hc.ne_top).symm

theorem source_common_normal_of_A312
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
    (T : Sylow 2 G) (A H R : Subgroup G)
    (hA : A ∈ Chapter1.HOver G (T : Set G))
    (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hu : Order.HasUniqueMaximalOver (T : Subgroup G) H)
    (_hR : R ≠ ⊥) (hRT : R ≤ T)
    (hs : Chapter1.IsSylowIn 2 R ((pResidual 2 H).map H.subtype ⊔ R))
    (hn : A ≤ normalizer (R : Set G)) : HasCommonNormal A H R := by
  have hf : generalizedFitting H = pCore 2 H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hH))
  have hu' : Order.HasUniqueMaximalOver (T.subtype hH.2 : Subgroup H) ⊤ :=
    unique_maximal_subgroupOf hu
  rw [sup_comm] at hs
  obtain ⟨Q,hQ⟩ := hs
  obtain ⟨N,hne,hNR,hN⟩ := ChapterC.Section05.theorem_C_5_8_of_A_3_12
    hG hA312 T H A R hH.2 hf hu' hRT hA.2 hn Q hQ
  have hTA : (T : Subgroup G) ≤ A := hA.2
  have hNA : N ≤ A ⊔ H := hNR.trans (hRT.trans (hTA.trans le_sup_left))
  refine ⟨N,hNR,hne,normalIn_iff_le_normalizer.mpr ?_⟩
  rw [generated_eq_sup]
  exact ⟨hNA,(normal_subgroupOf_iff_le_normalizer hNA).mp hN⟩
end CFSG.Quasithin.Chapter3
