module
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer
public import CFSG.Quasithin.Chapter10.SourceNonnormalPushingSetup
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.Setup
public import Theory.GroupTheory.CharacteristicNormalizerRestriction

/-!
# The source C.2.3 pushing setup in the component normalizer

For the original nonnormal A₅ setup, `R = O₂(L₀T)` is the actual source
two-core. Source uniqueness controls its characteristic-normalizer closure
inside the maximal local group. Restricting the A.4.2(7) maximal-signalizer and
section-centralizer conclusions to an arbitrary SQTK overgroup containing L₀ and
R supplies every field of the C.2.3 pushing setup. Specializing to N_G(L)
uses the full half-Sylow orbit containment and the component-normalizer
quotient lifting. No Baumann-normalizer escape or quotient classification is
assumed here; C.2.7 still requires its independent quasisimple component field.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
10.2.6 and C.2.3, printed pp.748–749 and 144–145.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterA.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D
private theorem uniqueness : Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

/-- The source uniqueness subgroup controls all characteristic normalizers of R. -/
theorem source_join_core_characteristic_control :
    ((localJoin T L).pCoreIn 2).characteristicNormalizerClosure ≤ D.maximalLocal := by
  exact characteristicNormalizerClosure_le_of_unique_maximalTwoLocal
    (D.lemma_3_2_3_uniqueness (uniqueness D)).2.2 (isPGroup_pCoreIn 2 _)
    ((localJoin T L).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))

/-- The literal O₂(L₀T) is nontrivial. -/
theorem source_join_core_ne_bot : (localJoin T L).pCoreIn 2 ≠ ⊥ :=
  fun h => D.module_ne_bot (bot_unique (D.module_le_core.trans_eq h))

omit D [Finite G] in
private theorem radical_restrict {X R H : Subgroup G}
    (hne : R ≠ ⊥) (hXH : X ≤ H) (hRH : R ≤ H)
    (hR : IsMaximalTwoSignalizer X ⊤ R) : IsPRadical 2 (R.subgroupOf H) := by
  have hm := (isMaximalTwoSignalizer_iff _ _ _).mp hR
  let N := H ⊓ normalizer (R : Set G)
  have hXN : X ≤ N := le_inf hXH hm.1.normalizes
  have hRN : R ≤ N := le_inf hRH le_normalizer
  have hRB : R ≤ N.pCoreIn 2 := le_pCoreIn_of_normalizes hm.1.isPGroup hRN inf_le_right
  have hBN : X ≤ normalizer (N.pCoreIn 2 : Set G) := hXN.trans
    (N.le_normalizer.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N)))
  have hBR : N.pCoreIn 2 ≤ R := hm.2 _
    ((isTwoSignalizer_iff _ _ _).mpr ⟨le_top, isPGroup_pCoreIn 2 N, hBN⟩) hRB
  have he : N.pCoreIn 2 = R := le_antisymm hBR hRB
  refine ⟨?_, ?_⟩
  · intro hb
    apply hne
    simpa only [map_subgroupOf_eq_of_le hRH, Subgroup.map_bot] using
      congrArg (map H.subtype) hb
  · apply map_injective H.subtype_injective
    change ((normalizer (R.subgroupOf H : Set H)).pCoreIn 2).map H.subtype = _
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective,
      ← subgroupOf_normalizer_eq hRH, subgroupOf_map_subtype]
    simpa only [inf_comm, map_subgroupOf_eq_of_le hRH] using he

/-- C.2.3 for any source overgroup containing L₀ and the original R. -/
theorem source_join_core_pushing_setup {H : Subgroup G}
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hXH : localOrbit T L ≤ H) (hRH : (localJoin T L).pCoreIn 2 ≤ H) :
    Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple H
      ((localJoin T L).pCoreIn 2) (H ⊓ D.maximalLocal) := by
  let X := localOrbit T L
  let R := (localJoin T L).pCoreIn 2
  let M := D.maximalLocal
  have hXM : X ≤ M := X.le_normalizer
  have hMX : M ≤ normalizer (X : Set G) := le_rfl
  have hXP : IsPPerfect 2 X := (pResidual_eq_top_iff 2 _).mp D.orbit_residual
  have hTM : (T : Subgroup G) ≤ M := le_normalizer_componentOrbit L T
  have hRM : R ≤ M := (pCoreIn_le 2 _).trans (sup_le hXM hTM)
  have hctrl := source_join_core_characteristic_control D
  have hNR : normalizer (R : Set G) ≤ M :=
    (normalizer_le_characteristicNormalizerClosure_self R (source_join_core_ne_bot D)).trans hctrl
  have hc := normal_sylow_core_conclusions X M hXM hMX hXP (T.subtype hTM)
    (by simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM] using hNR)
  simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM] at hc
  have hmax : IsMaximalTwoSignalizer X ⊤ R := hc.2.2.1
  have hlocal := (isMaximalTwoSignalizer_iff _ _ _).mp hc.2.2.2.1
  have hn : (X.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hMX
  have hRC := signalizer_le_twoSectionCentralizer X M R hXM hn.isSubnormal hXP hlocal.1
  have hsyl : Chapter1.IsSylowIn 2 R (twoSectionCentralizer X M) :=
    (maximal_signalizer_iff_sylow X M R hXM hn.isSubnormal hXP).mp hc.2.2.2.1
  refine ⟨hH,hRH,inf_le_left,radical_restrict (source_join_core_ne_bot D) hXH hRH hmax,?_,?_⟩
  · intro g hg
    exact ⟨g.property,characteristicNormalizerClosure_subgroupOf_le hRH hctrl hg⟩
  · apply hsyl.restrict
    · have hr := map_mono (f := (H ⊓ M).subtype)
        (le_normalClosure (H := R.subgroupOf (H ⊓ M)))
      simpa only [R, map_subgroupOf_eq_of_le (le_inf hRH hRM)] using hr
    · let C := twoSectionCentralizer X M
      let _ : (C.subgroupOf (H ⊓ M)).Normal := normal_subgroupOf_of_le_normalizer
        (inf_le_right.trans (twoSectionCentralizer_normalized X M hMX))
      exact (map_le_iff_le_comap).mpr
        (normalClosure_le_normal (N := C.subgroupOf (H ⊓ M)) (fun _ hr => hRC hr))

/-- The original local two-core normalizes the original C-component. -/
theorem source_join_core_le_component_normalizer :
    (localJoin T L).pCoreIn 2 ≤ normalizer (L : Set G) := by
  let J := localJoin T L
  have hLJ : L ≤ J := (le_componentOrbit L T).trans le_sup_left
  have hL : (L.subgroupOf J).IsCComponent := by
    dsimp [J]
    change (L.subgroupOf (localOrbit T L ⊔ (T : Subgroup G))).IsCComponent
    apply D.maximal.1.1.subgroupOf_of_le
      (show L ≤ localOrbit T L ⊔ (T : Subgroup G) from
        (le_componentOrbit L T).trans le_sup_left)
    exact (componentOrbit_sup L T).le
  let _ := pCore_isNilpotent (p := 2) (G := J)
  have hQ : pCore 2 J ≤ normalizer (L.subgroupOf J : Set J) := by
    rw [←normalizer_cComponent_quotient hL (pCore 2 J)]
    intro x hx
    show QuotientGroup.mk' (pCore 2 J) x ∈
      normalizer ((L.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) : Set (J ⧸ pCore 2 J))
    have hqx : QuotientGroup.mk' (pCore 2 J) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hx
    rw [hqx]
    exact one_mem _
  have hh := map_mono (f := J.subtype) hQ
  rw [←subgroupOf_normalizer_eq hLJ,subgroupOf_map_subtype] at hh
  exact hh.trans inf_le_left

/-- The actual C.2.3 setup in the full component normalizer, with R=O₂(L₀T). -/
theorem source_nonnormal_component_normalizer_pushing_setup
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple
      (normalizer (L : Set G)) ((localJoin T L).pCoreIn 2)
      (normalizer (L : Set G) ⊓ D.maximalLocal) :=
  source_join_core_pushing_setup D (source_component_normalizer_sqtk D)
    (source_nonnormal_orbit_le_normalizer D hn) (source_join_core_le_component_normalizer D)
end CFSG.Quasithin.Chapter10
