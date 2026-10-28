module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.RankOne
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwoSource
public import Theory.GroupTheory.CComponent.OrbitCorrespondence
public import Theory.GroupTheory.CComponent.NonsolvableNormalIntersection

/-!
# A binary rank-one orbit cannot enlarge the original replacement orbit

Select the containing C-component using the proved full-Sylow containment
part of A.3.12. Normality of the actual X-span puts this component inside
that span. Inside IT its component is a T-conjugate of I, so the actual
binary model transports to it. Rank-one non-enlargement then identifies
it with the original replacement component, including both two-cores.

Source: Aschbacher--Smith §10.3, printed pp.756--757.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups
open Chapter3.Section02
open Theory.SpecificGroups.SymmetricFive.WreathComponents
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D}

/-- The remaining binary alternative of 10.2.4 implies the literal span
identity; no containing-component hypothesis is left to the caller. -/
theorem span_eq_of_binary_orbit
    (d : CentralizerData T D s)
    (e : (componentJoin T L (d.first * d.second) ⧸
      pCore 2 (componentJoin T L (d.first * d.second))) ≃* W)
    (hstrict : centralizerSeed T L (d.first * d.second) <
      componentSpan T L (d.first * d.second))
    (horbit : ∀ K ∈ Chapter1.cComponentsIn (componentJoin T L (d.first * d.second)),
      componentOrbit K (T : Subgroup G) = componentSpan T L (d.first * d.second))
    {M I : Subgroup G} (hM : IsMaximalTwoLocal M)
    (hJM : componentJoin T L (d.first * d.second) ≤ M)
    (hI : I ∈ Chapter1.cComponentsIn M)
    (hq : IsQuasisimple (I ⧸ pCore 2 I))
    {n : ℕ} (hmodel : ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 2 (2 ^ n))
    (hgen : conjugateSpanBy (centralizerSeed T L (d.first * d.second)) M =
      componentOrbit I (T : Subgroup G)) :
    conjugateSpanBy (centralizerSeed T L (d.first * d.second)) M =
      componentSpan T L (d.first * d.second) := by
  let z := d.first * d.second
  let X := centralizerSeed T L z
  let J := componentJoin T L z
  let N := conjugateSpanBy X M
  have hTM : (T : Subgroup G) ≤ M := le_sup_right.trans hJM
  have hNM : N ≤ M := conjugateSpanBy_le_self
    (((le_conjugateSpanBy X (centralizer ({z} : Set G))).trans le_sup_left).trans hJM)
  have hKN := componentSpan_le_overgroup_span d e hstrict horbit hJM
  obtain ⟨K,hK⟩ := exists_component_of_wreath e
  have hlocal := (component_of_wreath (T := T) le_sup_right d.join_core_ne_bot e hK).1
  have hKM : K ≤ M := hK.1.trans hJM
  have hKN' : K ≤ N := ((le_componentOrbit K T).trans_eq (horbit K hK)).trans hKN
  let S := T.subtype hTM
  have hlocalM : K.subgroupOf M ∈ Chapter1.L M (S : Subgroup M) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTM hKM).mp ⟨hKM,hlocal⟩
  have hQ := Chapter1.Section02.uniqueness_local_quotient_sqtk D.simpleQTKE
    (Chapter1.mem_H_of_isTwoLocal hM.1)
  obtain ⟨B,⟨hB,hKB⟩,_⟩ := Chapter1.Section02.index_le_two_local_component_source
    hQ S (le_rfl : (S : Subgroup M) ≤ S) (by simp) hlocalM
  let : (N.subgroupOf M).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy X M)
  have hKns : ¬ Group.IsSolvable (K.subgroupOf M) := by
    intro hs
    let := hs
    let a := subgroupOfEquivOfLe
      (show K.subgroupOf M ≤ K.subgroupOf M ⊔ (S : Subgroup M) from le_sup_left)
    exact hlocalM.1.not_isSolvable (Group.isSolvable_of_surjective
      (f := a.symm.toMonoidHom) a.symm.surjective)
  have hBN : B ≤ N.subgroupOf M :=
    hB.le_normal_of_nonsolvable_subgroup hKns hKB (comap_mono hKN')
  let Y := I ⊔ (T : Subgroup G)
  have hYM : Y ≤ M := sup_le hI.1 hTM
  have hNY : N ≤ Y := hgen.le.trans (componentOrbit_le_sup I T)
  have hBY : B.map M.subtype ≤ Y := (map_mono hBN).trans
    ((map_subgroupOf_eq_of_le hNM).le.trans hNY)
  let B₀ := B.map M.subtype
  have hB₀ : B₀ ∈ Chapter1.cComponentsIn M := by
    refine ⟨map_subtype_le _,?_⟩
    simpa only [B₀,subgroupOf,comap_map_eq_self_of_injective M.subtype_injective] using hB
  have hIY := hI.2.subgroupOf_of_le (show I ≤ Y from le_sup_left) hYM
  have hBYcomp := hB₀.2.subgroupOf_of_le hBY hYM
  let R := T.subtype (show (T : Subgroup G) ≤ Y from le_sup_right)
  have hygen : I.subgroupOf Y ⊔ (R : Subgroup Y) = ⊤ := by
    change I.subgroupOf Y ⊔ (T : Subgroup G).subgroupOf Y = ⊤
    rw [←subgroupOf_sup (show I ≤ Y from le_sup_left)
      (show (T : Subgroup G) ≤ Y from le_sup_right),subgroupOf_self]
  obtain ⟨t,ht⟩ := hIY.conjugate_of_pGroup_generated hBYcomp R.isPGroup' hygen
  have htG : (t : Y).val ∈ (T : Subgroup G) := t.property
  have he : B₀ = I.map (MulAut.conj ((t : Y) : G)).toMonoidHom := by
    have hh := congrArg (map Y.subtype) ht
    rw [map_subgroupOf_eq_of_le hBY,map_map] at hh
    change B₀ = (I.subgroupOf Y).map
      ((MulAut.conj ((t : Y) : G)).toMonoidHom.comp Y.subtype) at hh
    rw [←map_map,map_subgroupOf_eq_of_le (show I ≤ Y from le_sup_left)] at hh
    exact hh
  let a : I ≃* B₀ := (I.equivMapOfInjective
    (MulAut.conj ((t : Y) : G)).toMonoidHom (MulAut.conj _).injective).trans
      (MulEquiv.subgroupCongr he.symm)
  let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hqB : IsQuasisimple (B₀ ⧸ pCore 2 B₀) := by
    let := hq
    exact IsQuasisimple.of_mulEquiv b
  have hmB : ClassicalGroup.IsPSL (B₀ ⧸ pCore 2 B₀) 2 (2 ^ n) :=
    hmodel.of_mulEquiv b.symm
  have hKB₀ : K ≤ B₀ := by
    have hh := map_mono (f := M.subtype) hKB
    rwa [map_subgroupOf_eq_of_le hKM] at hh
  have hKeq : K = B₀ := component_eq_binary_overcomponent d e hK hJM hB₀ hKB₀ hqB hmB
  have hIB : I ≤ componentOrbit B₀ (T : Subgroup G) := by
    intro i hi
    have hc : (MulAut.conj ((t : Y) : G)) i ∈ B₀ := he.symm ▸ mem_map_of_mem _ hi
    exact (mem_normalizer_iff.mp (le_normalizer_componentOrbit B₀ T htG) i).mpr
      ((le_componentOrbit B₀ T) hc)
  apply le_antisymm ?_ hKN
  rw [hgen, ←horbit K hK, hKeq]
  exact iSup_conjugates_le_of_le_normalizer I T _ hIB
    (le_normalizer_componentOrbit B₀ T)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups
