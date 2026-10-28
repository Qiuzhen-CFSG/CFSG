module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ComponentOrbitBound
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.RelativeComponents.DirectFive

/-!
# The original A₅ component exclusion from noncentral A.3.6

The actual two-core quotient of H is SQTK. The orbit bound from A.3.7
lifts through that quotient's canonical map and makes the original span
Y = conjugateSpanBy K T normal in H. Perfectness follows from the chosen
relative C-component. The existing DirectFive argument then excludes
K ≤ M using the original A₅ quotient and unique maximal two-local.

Only the genuine universal noncentral A.3.6 implication remains explicit;
its producer is `qt-a03-noncentral-fitting-structure`. The source 13.6
assembly retains its discharge. No model classification, normality of
the chosen component, or target-specific orbit property is assumed.

Source: Aschbacher--Smith A.3.8(3) and 13.6.26(1), pp.46 and 934.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original relative component has a normal perfect T-span, using
only the genuine noncentral structural input through A.3.7. -/
theorem relative_component_span_properties_of_noncentral_structure
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h36 : ChapterA.Section03.CComponentCommutation.NoncentralStructureInput.{u}
      KnownSimple.IsKnownSimple)
    (T : Sylow 2 G) {H K : Subgroup G} (hH : H ∈ Chapter1.H G)
    (hTH : (T : Subgroup G) ≤ H) (hK : K ∈ Chapter1.cComponentsIn H) :
    conjugateSpanBy K T ≤ H ∧
      H ≤ normalizer (conjugateSpanBy K T : Set G) ∧
      Group.IsPerfect (conjugateSpanBy K T) ∧ IsPPerfect 2 (conjugateSpanBy K T) := by
  have := pCore_isNilpotent (p := 2) (G := H)
  have hquot := ChapterA.Section03.ComponentOrbitBound.normal_or_index_two_of_noncentral_structure
    h36 (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hH)
    (pCore_quotient_pCore_eq_bot 2) (hK.2.map_quotient (pCore 2 H))
  have horbit := cComponent_normal_or_index_two_of_quotient hK.2 (pCore 2 H) hquot
  let S := T.subtype hTH
  let D := conjugateSpanBy (K.subgroupOf H) (S : Subgroup H)
  have hn : D.Normal := conjugateSpanBy_sylow_normal _ S horbit
  have he : D.map H.subtype = conjugateSpanBy K T := by
    rw [map_conjugateSpanBy]
    simp only [S, Sylow.coe_subtype, map_subgroupOf_eq_of_le hK.1,
      map_subgroupOf_eq_of_le hTH]
  have hd : (D.map H.subtype).subgroupOf H = D :=
    comap_map_eq_self_of_injective H.subtype_injective D
  have hrel : ((conjugateSpanBy K T).subgroupOf H).Normal := by
    rw [← he, hd]
    exact hn
  have hYH : conjugateSpanBy K T ≤ H :=
    conjugateSpanBy_le hK.1 (hTH.trans H.le_normalizer)
  have hHY : H ≤ normalizer (conjugateSpanBy K T : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYH).mp hrel
  have : Group.IsPerfect (K.subgroupOf H) := hK.2.perfect
  have : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hK.1).toMonoidHom) (subgroupOfEquivOfLe hK.1).surjective
  have hperfect := conjugateSpanBy_isPerfect K (T : Subgroup G)
  refine ⟨hYH, hHY, hperfect, ?_⟩
  intro N hN hq
  have := hN
  by_contra hne
  have : Nontrivial (conjugateSpanBy K T ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  have : Group.IsPerfect (conjugateSpanBy K T ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  exact Group.IsPerfect.not_isNilpotent (conjugateSpanBy K T ⧸ N) hq.isNilpotent

/-- The complete 13.6.26(1) conclusion for the original A₅ setup, with
only noncentral A.3.6 retained instead of the full A.3.8 model theorem. -/
theorem source_13_6_26_1_of_A5_setup_of_noncentral_structure
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h36 : ChapterA.Section03.CComponentCommutation.NoncentralStructureInput.{u}
      KnownSimple.IsKnownSimple)
    (T : Sylow 2 G) (L V M MV L₁ G₁ : Subgroup G)
    [IsElementaryAbelian 2 V]
    (s : EarlierA5Setup T L V M MV)
    {H : Subgroup G} (hH : H ∈ Chapter13.Section08.Source.Hz L₁ T G₁ M) :
    ∀ K ∈ Chapter1.cComponentsIn H, ¬ K ≤ M := by
  intro K hK hKM
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  obtain ⟨hYH, hHY, hperfect, hp⟩ :=
    relative_component_span_properties_of_noncentral_structure hG h36 T hH.1.1 hTH hK
  have := hperfect
  have hTM : (T : Subgroup G) ≤ M := le_sup_right.trans
    (show M ∈ maximalTwoLocalOvergroups (L ⊔ (T : Subgroup G)) from
      s.unique_overgroup.symm ▸ Set.mem_singleton M).2
  have hYM : conjugateSpanBy K T ≤ M :=
    conjugateSpanBy_le hKM (hTM.trans M.le_normalizer)
  have hYne : conjugateSpanBy K T ≠ ⊥ := by
    intro hz
    have hKbot : K = ⊥ := bot_unique ((le_conjugateSpanBy K T).trans_eq hz)
    have hrel : K.subgroupOf H = ⊥ := by rw [hKbot]; simp
    apply hK.2.not_isSolvable
    rw [hrel]
    infer_instance
  exact perfect_normal_span_excluded hG T L M H (conjugateSpanBy K T)
    s.quotient s.local_normalizer s.unique_overgroup ⟨⟨hH.1.1, hTH⟩, hH.2.2⟩
    hYH hHY hp hYne hYM

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters
