module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFactors
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalBlockMaximal
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo

/-!
# Core normality and the two remaining unitary maximality cases

Let K = O²(H), Q = O₂(K), and let J be a maximal local overcomponent of
K. If J normalizes Q, source 1.2.7 puts J in the C-components of N_G(Q).
The nonsolvable subgroup K has a unique containing C-component there,
so N_G(K) normalizes J. Consequently the full right parabolic and T
normalize O₂(J). The original enlarged-core identity from 5.2.7 forces
O₂(J) = Q, including in the degree-two unitary extension. No equality
between O₂(H) and Q is used.

The ordinary and extended unitary factor comparisons give the actual
right quotient PSL₂(2^m), with original n = 2m. The binary embedding
selection now forces m = 2 for a proper J with normal Q, and identifies
J/O₂(J) with one of the five actual A.3.14 models. Therefore every
unitary comparison either has maximal K or has a proper maximal J with
nonnormal Q, or has this precise field-four configuration. The literal
normalizer application discharges the common Sylow and enlarged cores
while retaining these two source cases as conclusions.

The nonnormal-core argument and the field-four representation exclusions
remain to be proved; this module does not assert unitary maximality or
GlobalExit. Exhaustive F.1.12 comparison, original left uniqueness and
ambient completion recognition also remain separate obligations in this
task. All comparisons retain S = O₂(N_G(L) ∩ H), both odd Cartans in the
whole overlap, and both orientations. Source: Aschbacher–Smith 5.2.8,
printed pp.652–653, and 1.2.7 and A.3.12–14 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

private theorem maximal_normalizes_of_core_normal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {K J : Subgroup G}
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    (hQ : K.pCoreIn 2 ≠ ⊥)
    (hn : J ≤ normalizer (K.pCoreIn 2 : Set G)) :
    normalizer (K : Set G) ≤ normalizer (J : Set G) := by
  let Q := K.pCoreIn 2
  let N := normalizer (Q : Set G)
  have hKN : K ≤ N := K.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hNN : normalizer (K : Set G) ≤ N :=
    normalizer_le_normalizer_characteristic_image K (pCore 2 K)
  have hTN : (T : Subgroup G) ≤ N := hTK.trans hNN
  have hN : N ∈ Chapter1.H G :=
    Chapter1.mem_H_of_isTwoLocal ⟨Q,hQ,isPGroup_pCoreIn 2 K,rfl⟩
  have hj := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple hG T hJ).component
    N ⟨hN,sup_le hn hTN⟩
  have hnot : ¬ Group.IsSolvable (K.subgroupOf N) := by
    intro hs
    let := hs
    exact Chapter1.mem_L_not_isSolvable hK
      (Group.isSolvable_of_surjective (f := (subgroupOfEquivOfLe hKN).toMonoidHom)
        (subgroupOfEquivOfLe hKN).surjective)
  have hh := cComponent_le_normalizer_of_unique hj (comap_mono hKJ)
    (fun D hD hKD => Chapter1.Section02.IndexTwo.cComponent_unique_over_nonsolvable
      hnot hD hj hKD (comap_mono hKJ))
    (S := (normalizer (K : Set G)).subgroupOf N)
    (by
      change (normalizer (K : Set G)).subgroupOf N ≤ normalizer (K.subgroupOf N : Set N)
      rw [←subgroupOf_normalizer_eq hKN])
  rw [←subgroupOf_normalizer_eq hn] at hh
  intro x hx
  exact hh (show (⟨x,hNN hx⟩ : N) ∈ (normalizer (K : Set G)).subgroupOf N from hx)

/-- Normality of the original right core in a maximal local overcomponent
forces exact core equality and normalization by the whole N_G(K). The
literal enlarged-parabolic core identity is supplied by the comparison. -/
theorem Preparation.maximal_overcomponent_core_of_normal
    {T : Sylow 2 G} {L W H A B J : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (hc : ConcreteAmalgamComparison
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)))
    (hK : residual H ∈ Chapter1.L G (T : Subgroup G))
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : residual H ≤ J)
    (hn : J ≤ normalizer ((residual H).pCoreIn 2 : Set G)) :
    J.pCoreIn 2 = (residual H).pCoreIn 2 ∧
      normalizer (residual H : Set G) ≤ normalizer (J : Set G) := by
  let K := residual H
  let P := ChapterF.Source.parabolic ![L,K] (sourceS L H) 1
  let Y := P ⊔ (T : Subgroup G)
  have hTK := hTH.trans (le_normalizer_residual H)
  have hQ : K.pCoreIn 2 ≠ ⊥ := by
    have hchar := Chapter1.mem_He_iff.mpr
      (Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T (h.qtke.evenCharacteristic T) hK)
    intro hb
    change K ⊓ centralizer (K.pCoreIn 2 : Set G) ≤ K.pCoreIn 2 at hchar
    have hz : centralizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      centralizer_eq_top_iff_subset.mpr (show (⊥ : Subgroup G) ≤ center G from bot_le)
    rw [hb,hz,inf_top_eq] at hchar
    exact d.right_outside (hchar.trans bot_le)
  have hNJ := maximal_normalizes_of_core_normal h.qtke hK hTK hJ hKJ hQ hn
  have hPK : P ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (show K ≤ P from le_sup_left.trans le_sup_left)).mp
        ((d.hypothesisF11 h hTH).local_normal_in_parabolic 1)
  have hYJ : Y ≤ normalizer (J : Set G) := (sup_le hPK hTK).trans hNJ
  have hRY : J.pCoreIn 2 ≤ Y := by
    have hHJ : H ≤ J ⊔ (T : Subgroup G) := by
      rw [←residual_sup_sylow T H hTH]
      exact sup_le_sup hKJ le_rfl
    have hRH : J.pCoreIn 2 ≤ H.pCoreIn 2 :=
      (pCoreAmbient_mono_of_isSubnormalIn J (J ⊔ (T : Subgroup G)) 2
        le_sup_left hJ.1.1.subnormal).trans
        (Chapter3.twoCore_le_of_sylow_le T hTH hHJ)
    exact (hRH.trans (Chapter3.twoCore_le_of_sylow_le T (le_inf h.sylow_normalizes hTH)
      inf_le_right)).trans ((sourceS_le_sylow h.sylow_normalizes hTH).trans le_sup_right)
  have he : Y.pCoreIn 2 = K.pCoreIn 2 :=
    d.parabolic_sylow_core_eq_of_comparison h hTH hp hc 1
  refine ⟨le_antisymm ?_ (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K)
    ((map_subtype_le _).trans hKJ) hn),hNJ⟩
  exact (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 J) hRY
    (hYJ.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))).trans_eq he

open ChapterF.GreenBook.LieModels.UnitaryFour
section Unitary
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
  (he : (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse)) ∨
    (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)))
include d h hH hp m hm he

/-- A proper maximal overcomponent that normalizes the original unitary core
has exactly that core. Its quotient lies in the actual A.3.14 shortlist,
and the original left exponent is four, not two. -/
theorem Preparation.unitary_overcomponent_parameter_of_normal
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H < J)
    (hn : J ≤ normalizer ((residual H).pCoreIn 2 : Set G)) :
    m = 2 ∧ n = 4 ∧ J.pCoreIn 2 = (residual H).pCoreIn 2 ∧
      ChapterA.Section03.SourceEmbeddings.AlternatingFive.Shortlist
        (J ⧸ pCore 2 J) := by
  have hf := he.elim (d.unitary_local_structure h hH.1.1.2 hp m hm)
    (d.unitaryExtension_local_structure h hH.1.1.2 hp m hm)
  obtain ⟨hm',hn',_,_,hb⟩ := hf
  have hc : ConcreteAmalgamComparison
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) :=
    he.elim (.unitary m hm) (.unitaryExtension m hm)
  have hK := residual_binary_mem_local hH.1.1 hp hm' hb
  have hcore := (d.maximal_overcomponent_core_of_normal h hH.1.1.2 hp hc hK hJ hKJ.le hn).1
  have hh := local_binary_overcomponent_of_core_eq h.qtke hJ.1
    (hH.1.1.2.trans (le_normalizer_residual H)) hKJ hcore hm' hp hb
  exact ⟨hh.1,by omega,hcore,hh.2⟩

/-- The two remaining unitary cases of 5.2.8, on the actual prepared pair:
a proper maximal overcomponent either fails to normalize O₂(K), or the
field is four and its quotient belongs to the five actual A.3.14 models.
The degree-two extension is included without equating O₂(H) and O₂(K). -/
theorem Preparation.unitary_maximal_or_obstruction :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) ∨
      ∃ J ∈ Chapter1.LStar G (T : Subgroup G), residual H < J ∧
        (¬ J ≤ normalizer ((residual H).pCoreIn 2 : Set G) ∨
          m = 2 ∧ n = 4 ∧ J.pCoreIn 2 = (residual H).pCoreIn 2 ∧
            ChapterA.Section03.SourceEmbeddings.AlternatingFive.Shortlist
              (J ⧸ pCore 2 J)) := by
  by_cases hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G)
  · exact .inl hmax
  right
  have hf := he.elim (d.unitary_local_structure h hH.1.1.2 hp m hm)
    (d.unitaryExtension_local_structure h hH.1.1.2 hp m hm)
  have hK := residual_binary_mem_local hH.1.1 hp hf.1 hf.2.2.2.2
  obtain ⟨J,hJ,hKJ⟩ := Chapter1.exists_mem_LStar_ge hK
  have hlt : residual H < J := lt_of_le_of_ne hKJ (fun hh => hmax (hh.symm ▸ hJ))
  refine ⟨J,hJ,hlt,?_⟩
  by_cases hn : J ≤ normalizer ((residual H).pCoreIn 2 : Set G)
  · exact .inr (d.unitary_overcomponent_parameter_of_normal h hH hp m hm he hJ hlt hn)
  · exact .inl hn

/-- The original normalizer pair satisfies the 5.3 local conditions unless
one of the two explicitly identified unitary maximality cases occurs.
Neither core normality nor exclusion of the field-four row is assumed. -/
theorem Preparation.unitary_normalizer_or_obstruction :
    Chapter5.Section03GreenExtension.SourceLocalConditions
      (normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) ∨
      ∃ J ∈ Chapter1.LStar G (T : Subgroup G), residual H < J ∧
        (¬ J ≤ normalizer ((residual H).pCoreIn 2 : Set G) ∨
          m = 2 ∧ n = 4 ∧ J.pCoreIn 2 = (residual H).pCoreIn 2 ∧
            ChapterA.Section03.SourceEmbeddings.AlternatingFive.Shortlist
              (J ⧸ pCore 2 J)) := by
  rcases d.unitary_maximal_or_obstruction h hH hp m hm he with hmax | hh
  · left
    have hc : ConcreteAmalgamComparison
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) :=
      he.elim (.unitary m hm) (.unitaryExtension m hm)
    exact d.normalizer_local_conditions h hH hmax rfl
      (d.common_sylow_of_comparison h hH.1.1.2 hp hc)
      (d.parabolic_sylow_core_eq_of_comparison h hH.1.1.2 hp hc)
  · exact .inr hh

end Unitary

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
