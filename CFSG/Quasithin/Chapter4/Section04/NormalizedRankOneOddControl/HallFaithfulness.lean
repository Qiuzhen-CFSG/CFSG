module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.Complete
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.KnownSimple
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.Chapter4.Section01.NormalizerUniqueness
public import Theory.GroupTheory.Hall.Conjugacy
import Mathlib.Tactic

/-!
# Hall faithfulness from normalized odd-normalizer control

For an H-star member with generation parameter greater than one, the actual
E.2.2 Cartan witness supplies an elementary odd subgroup in a nontrivial
section kernel. The full 4.4.13(1) normalizer-escape theorem contradicts
abelian odd-normalizer control when odd section actors centralize W.
Hall conjugacy in the solvable overlap transfers faithfulness from this
witness to every prescribed Hall subgroup, retaining its ambient inclusion.

Both the abelian control and module-centralization premises remain explicit.
The chosen-module adapter discharges the latter using the non-FF branch
of 3.1.8 and perfect residual covering; 4.4.3 remains to be proved.
Source: Aschbacher--Smith, Theorem 4.4.14 and Lemma 4.4.13,
printed pp.623--625.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
open ChapterB ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem hall_inf_eq_bot_transfer (M C Y B : Subgroup G)
    (hsolv : Group.IsSolvable M) (hYM : Y ≤ M) (hBM : B ≤ M)
    (hY : IsHallSubgroup oddPrimes (Y.subgroupOf M))
    (hB : IsHallSubgroup oddPrimes (B.subgroupOf M))
    (hMC : M ≤ normalizer (C : Set G)) (hYC : Y ⊓ C = ⊥) : B ⊓ C = ⊥ := by
  obtain ⟨g,hg⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable hsolv hY hB
  have he : B = Y.map (MulAut.conj (g : G)).toMonoidHom := by
    have hm := congrArg (Subgroup.map M.subtype) hg
    simpa only [map_subgroupOf_eq_of_le hBM, map_subgroupOf_map_conj_eq hYM] using hm
  have hC : C.map (MulAut.conj (g : G)).toMonoidHom = C :=
    mem_normalizer_iff_map_conj_eq.mp (hMC g.property)
  rw [he, ← hC, ← Subgroup.map_inf Y C _ (MulAut.conj (g : G)).injective,
    hYC, Subgroup.map_bot]

/-- The Hall conclusion on the original section kernel follows from abelian
odd-normalizer control and the actual centralization of odd section actors.
No abelianness or permutation assumption on the prescribed Hall subgroup
is needed: the marked witness is transferred by Hall conjugacy. -/
theorem hall_faithful_of_abelian_odd_control
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G) (L W : Subgroup G)
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcontrol : ∀ A : Subgroup G, A ≠ ⊥ →
      A ≤ normalizer (L : Set G) ⊓ centralizer (W : Set G) →
      Odd (Nat.card A) → IsMulCommutative A →
      normalizer (A : Set G) ≤ normalizer (L : Set G))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlarge : 1 < generationParameter H)
    (hcentral : ∀ A : Subgroup G, A ≤ H → A ≤ sectionCentralizer L →
      Odd (Nat.card A) → A ≤ centralizer (W : Set G))
    (B : Subgroup H) (hBM : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H))) :
    B.map H.subtype ⊓ sectionCentralizer L = ⊥ := by
  let M := normalizer (L : Set G)
  let S := T.subtype hH.1.1.2
  have hP : IsMinimalParabolicOver S ⊤ := by
    apply minimalParabolic_subtype T H
    apply Chapter3.HStar.minimalParabolic T hTM hH
    right
    intro hn
    let : Group.IsSolvable H := IsTwoClosed.isSolvable ⟨T.subtype hH.1.1.2,hn⟩
    exact (not_lt_of_ge generationParameter_le_one_of_solvable) hlarge
  have he : minimalParabolicMax S hP = M.subgroupOf H := by
    let J := minimalParabolicMax S hP
    have hj := minimalParabolicMax_spec S hP
    have hTJ : (T : Subgroup G) ≤ J.map H.subtype := by
      have hh := map_mono (f := H.subtype) hj.2
      change ((T : Subgroup G).subgroupOf H).map H.subtype ≤ J.map H.subtype at hh
      rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
    have hJH : J.map H.subtype < H := by
      have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hj.1.lt_top
      change J.map H.subtype < (⊤ : Subgroup H).map H.subtype at hh
      simpa only [← MonoidHom.range_eq_map,range_subtype] using hh
    have hJM : J ≤ M.subgroupOf H := map_le_iff_le_comap.mp
      (Chapter3.HStar.proper_overgroup_le T hH hTJ hJH)
    have hn : M.subgroupOf H ≠ ⊤ := fun hh => hH.1.2 (subgroupOf_eq_top.mp hh)
    exact ((hj.1.le_iff.mp hJM).resolve_left hn).symm
  obtain ⟨n,hgen,hbound,d,_⟩ := MarkedModels.Inverted.source_intrinsic_escape_knownSimple
    (Chapter3.sqtk_of_mem_H hG hH.1.1.1) S hP hlarge
  let C := sectionCentralizer L
  have hCM : C ≤ M := ((le_sectionCentralizer_iff C L).mp le_rfl).1
  have hMC : M ≤ normalizer (C : Set G) := by
    have hh := sectionCentralizerIn_normalized (M := M) (X := L) le_rfl
    rwa [sectionCentralizerIn,inf_eq_right.mpr hCM] at hh
  have hTC : (S : Subgroup H) ≤ normalizer (C.subgroupOf H : Set H) :=
    (comap_mono (hTM.trans hMC)).trans (le_normalizer_comap H.subtype)
  have hYker : d.witness.abelianGroup ⊓ C.subgroupOf H = ⊥ := by
    by_contra hne
    obtain ⟨p,A,hp,ho,hA,hAe,hAY,hAo,hperm⟩ :=
      exists_elementary_odd_invariant_permuting d.witness.abelian d.witness.odd hne
        hTC d.frattini d.normalizes
    let := hAe
    have hcore : pCore 2 H ≠ ⊥ := by
      intro hh
      exact hH.1.1.1 (by simp only [pCoreIn,hh,Subgroup.map_bot])
    have htop := NormalizerEscape.source4413One_knownSimple G hG H inferInstance
      inferInstance H.subtype H.subtype_injective hcore hlarge S hP
      d.witness.abelianGroup d.hall_le d.hall p hp A hAe (hAY.trans inf_le_left) hperm
    have hAC : A.map H.subtype ≤ C := map_le_iff_le_comap.mpr (hAY.trans inf_le_right)
    have hAo' : Odd (Nat.card (A.map H.subtype)) := by
      rw [← Nat.card_congr (A.equivMapOfInjective H.subtype H.subtype_injective).toEquiv]
      exact hAo
    have hN := hcontrol (A.map H.subtype)
      (fun hh => hA ((map_eq_bot_iff_of_injective A H.subtype_injective).mp hh))
      (le_inf (hAC.trans hCM) (hcentral _ (map_subtype_le A) hAC hAo')) hAo' inferInstance
    have hNM : normalizer (A : Set H) ≤ M.subgroupOf H := by
      intro a ha
      exact hN (A.le_normalizer_map H.subtype (mem_map_of_mem H.subtype ha))
    apply hH.1.2
    apply subgroupOf_eq_top.mp
    apply top_unique
    rw [← htop,he]
    exact sup_le le_rfl hNM
  have hBM' : B ≤ minimalParabolicMax S hP := he.symm ▸ hBM
  have hHall' : IsHallSubgroup oddPrimes (B.subgroupOf (minimalParabolicMax S hP)) :=
    he.symm ▸ hHall
  have hBC := hall_inf_eq_bot_transfer (minimalParabolicMax S hP) (C.subgroupOf H)
    d.witness.abelianGroup B d.maximal_solvable d.hall_le hBM' d.hall hHall'
    (by rw [he]; exact (comap_mono hMC).trans (le_normalizer_comap H.subtype)) hYker
  apply eq_bot_iff.mpr
  rintro x ⟨⟨a,ha,rfl⟩,hc⟩
  have ha1 : a = 1 := hBC.le ⟨ha,hc⟩
  simp only [ha1,map_one,mem_bot]

end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
