module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceOrbits
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.SolvableSource

/-!
# Source 13.6.26 with its orbit and solvable-containment inputs proved

The unconditional C-component orbit theorem constructs the normal perfect
span of each original relative component under T. The actual five-point
argument then excludes this span from M. The solvable source of E.3.35
supplies the other clause on the same H_z family. The complete A.3.8 model
list and a universal E.3.35 callback are unnecessary for these deductions.

Only the genuine original A₅ setup and earlier 13.3.8(2) remain inputs.
The original component inclusion, T-span, and quotient-preimage O_{2,p}
are retained throughout.
Source: Aschbacher–Smith 13.6.26(1–2), printed p.934.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem relative_span_normal (T : Sylow 2 G) {H K : Subgroup G}
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (hK : (K.subgroupOf H).Normal ∨
      (normalizer (K.subgroupOf H : Set H)).index = 2) :
    H ≤ normalizer (conjugateSpanBy K T : Set G) := by
  let S := T.subtype hTH
  let D := conjugateSpanBy (K.subgroupOf H) (S : Subgroup H)
  have hn : D.Normal := conjugateSpanBy_sylow_normal _ S hK
  have he : D.map H.subtype = conjugateSpanBy K T := by
    rw [map_conjugateSpanBy]
    simp only [S, Sylow.coe_subtype, map_subgroupOf_eq_of_le hKH,
      map_subgroupOf_eq_of_le hTH]
  have hd : (D.map H.subtype).subgroupOf H = D :=
    comap_map_eq_self_of_injective H.subtype_injective D
  have hrel : ((conjugateSpanBy K T).subgroupOf H).Normal := by
    rw [← he, hd]
    exact hn
  exact (normal_subgroupOf_iff_le_normalizer
    (conjugateSpanBy_le hKH (hTH.trans H.le_normalizer))).mp hrel

private theorem perfect_twoPerfect {Y : Type*} [Group Y] [Finite Y]
    [Group.IsPerfect Y] : IsPPerfect 2 Y := by
  intro N hN hq
  let := hN
  by_contra hne
  let : Nontrivial (Y ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (Y ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  exact Group.IsPerfect.not_isNilpotent (Y ⧸ N) hq.isNilpotent

/-- Every relative C-component has a normal, perfect Sylow-conjugate span
inside the actual local overgroup. -/
theorem relative_component_span_properties_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    {H K : Subgroup G} (hH : H ∈ Chapter1.H G)
    (hTH : (T : Subgroup G) ≤ H) (hK : K ∈ Chapter1.cComponentsIn H) :
    conjugateSpanBy K T ≤ H ∧
      H ≤ normalizer (conjugateSpanBy K T : Set G) ∧
      Group.IsPerfect (conjugateSpanBy K T) ∧ IsPPerfect 2 (conjugateSpanBy K T) := by
  have horbit := Chapter1.Section02.proposition_1_2_1_three_orbit_source
    (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hH) hK.2
  let := hK.2.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hK.1).toMonoidHom) (subgroupOfEquivOfLe hK.1).surjective
  let hperfect := conjugateSpanBy_isPerfect K (T : Subgroup G)
  exact ⟨conjugateSpanBy_le hK.1 (hTH.trans H.le_normalizer),
    relative_span_normal T hK.1 hTH horbit,
    hperfect, perfect_twoPerfect⟩

/-- Source 13.6.26(1) from the actual earlier A₅ setup and the genuine A.3.8
orbit theorem. The original relative component and T-span are retained;
no 13.3.8 conclusion is requested as a premise. -/
theorem source_13_6_26_1_of_A5_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (L V M MV L₁ G₁ : Subgroup G)
    [IsElementaryAbelian 2 V]
    (s : EarlierA5Setup T L V M MV)
    {H : Subgroup G} (hH : H ∈ Chapter13.Section08.Source.Hz L₁ T G₁ M) :
    ∀ K ∈ Chapter1.cComponentsIn H, ¬ K ≤ M := by
  intro K hK hKM
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  obtain ⟨hYH, hHY, hperfect, hp⟩ :=
    relative_component_span_properties_source hG T hH.1.1 hTH hK
  let := hperfect
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

/-- Both original clauses, with orbit and E.3.35 inputs discharged. -/
theorem source_13_6_26_of_original_setup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {L V M MV : Subgroup G} [IsElementaryAbelian 2 V]
    (s : EarlierA5Setup T L V M MV) (h1338 : Earlier1338Two T)
    (L₁ G₁ : Subgroup G) :
    ∀ H ∈ Chapter13.Section08.Source.Hz L₁ (T : Subgroup G) G₁ M,
      (∀ K ∈ Chapter1.cComponentsIn H, ¬ K ≤ M) ∧
      (∀ p : ℕ, p.Prime → 3 < p → O2p H p = Chapter13.Section08.Source.QH H) := by
  intro H hH
  refine ⟨source_13_6_26_1_of_A5_source hG T L V M MV L₁ G₁ s hH, ?_⟩
  intro p hp hlarge
  let : Fact p.Prime := ⟨hp⟩
  exact source_13_6_26_2_of_solvable_source s s.localA_eq_one h1338 L₁ G₁ hH p hlarge

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters
