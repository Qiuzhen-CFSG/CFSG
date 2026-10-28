module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.OrdinaryComponents.ComponentData
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# Residual control on the escaping ordinary component

The nontrivial elementary moved module U_K lies inside K and is normalized
by H = KT. The earlier uniqueness for H therefore puts C_G(K) in Mc.
The ordinary component orbit has length at most two, so the two-perfect
K fixes each component. Both statements use the original subgroup embeddings
and do not assume that the component itself is normal in I.

Source: Aschbacher--Smith, proof of15.2.15, printed pp.1117--1118,
refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
open Section01 Section03 ChapterA.Section05To06 ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The original H uniqueness controls the entire centralizer of K = O²(H). -/
theorem residual_centralizer_le :
    centralizer ((pResidual 2 H).map H.subtype : Set G) ≤ Mc := by
  obtain ⟨hne, he, _, hT, hcomm⟩ := movedModule_data d
  let W := movedModule H V
  let K := (pResidual 2 H).map H.subtype
  have hKW : K ≤ normalizer (W : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr hcomm.le
  have hHW : H ≤ normalizer (W : Set G) := by
    rw [← d.residual_sup_sylow]
    exact sup_le hKW hT
  have hn : normalizer (W : Set G) ≤ Mc :=
    normalizer_le_of_unique_maximalTwoLocal
      (fun N hN hHN => Set.mem_singleton_iff.mp (d.local_unique ▸ ⟨hN, hHN⟩))
      he.isPGroup hne hHW
  have hHK : H ≤ normalizer (K : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))
  have hWK : W ≤ K := by
    change ⁅conjugateSpanBy V H,K⁆ ≤ K
    exact le_normalizer_iff_commutator_le_right.mp
      ((conjugateSpanBy_le_self (hsource.prepared.inside_core H d.geometry.outside |>.trans
        (twoCore_le H))).trans hHK)
  exact (centralizer_le hWK).trans ((Subgroup.centralizer_le_normalizer _).trans hn)

/-- Two-perfectness makes the original K normalize every ordinary component of I. -/
theorem component_residual_normalizes {I : Subgroup G} (hI : PlaneEscapes Mc ZS I)
    {L : Subgroup I} (hL : IsComponent I L) :
    (pResidual 2 H).map H.subtype ≤ normalizer (L.map I.subtype : Set G) := by
  let K := (pResidual 2 H).map H.subtype
  have hKI : K ≤ I :=
    (le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  let A := K.subgroupOf I
  have hpA : IsPPerfect 2 A := (isPPerfect_embedded_pResidual 2 H).of_surjective
    (subgroupOfEquivOfLe hKI).symm.toMonoidHom (subgroupOfEquivOfLe hKI).symm.surjective
  have hAN : A ≤ normalizer (L : Set I) := by
    rcases hL.normal_or_index_two_of_odd_rank_le_two
      (Chapter3.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin with hn | hi
    · let := hn
      rw [normalizer_eq_top]
      exact le_top
    · let N := normalizer (L : Set I)
      let : N.Normal := normal_of_index_eq_two hi
      have hq : IsPGroup 2 (I ⧸ N) := IsPGroup.of_card (n := 1) (by
        simpa only [← index_eq_card,pow_one] using hi)
      exact (le_pResidual_of_isPPerfect A hpA).trans (sInf_le ⟨inferInstance,hq⟩)
  intro k hk
  exact L.le_normalizer_map I.subtype
    (mem_map_of_mem I.subtype (hAN (show (⟨k,hKI hk⟩ : I) ∈ A from hk)))
end CFSG.Quasithin.Chapter15.Section02.OrdinaryComponents
