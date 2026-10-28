module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.Solvable
public import Theory.GroupTheory.PResidual.ConjugateGeneration

/-!
# The source component before rank-one recognition

The counterexample and the preceding 11.2.2 bound imply n(H) ≥ n > 1,
so H is nonsolvable. The genuine E.2.2 construction then supplies an
intrinsic C-component whose join with the prescribed Sylow is H. Its
ambient image has the same literal two-core quotient. Perfectness and
Sylow generation identify its H-conjugate span with the embedded O²(H).

The selected component escapes N_G(L), belongs to the actual local family,
and moves Ω₁Z(T). Its normality is only relative to H and is equivalent to
being all of O²(H). These are inputs for the two remaining arguments in
11.3.5: the model sieve at the actual generation parameter and the paired
Hall/Cartan exclusion. Neither argument is assumed by ComponentSeed, and
this module does not claim the final RankOneReduction.

Source: Aschbacher--Smith, 11.3.5, printed pp.771--772; the opening
component construction of E.2.2, printed pp.215--216 (combined manuscript,
1 March 2004).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H : Subgroup G}

/-- The constructed component and its actual ambient embeddings, before
any identification with a finite Lie-type model. -/
structure ComponentSeed (T : Sylow 2 G) (H K : Subgroup G) : Prop where
  component : Source.ComponentIn H K
  quasisimple : IsQuasisimple (K ⧸ pCore 2 K)
  supplement : K ⊔ (T : Subgroup G) = H
  span : residual H = Source.conjugateSpan H K

/-- The genuine generation lower bound excludes a solvable outside group.
The only extra bound is the preceding 11.2.2 conclusion on the original V. -/
theorem counterexample_not_solvable (h : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary) :
    ¬ Group.IsSolvable H := by
  intro hsolv
  let := hsolv
  have hu := ChapterE.generationParameter_le_one_of_solvable (G := H)
  have hl := degree_le_parameter h p hc hs
  have hn := S.nonbinary
  omega

private theorem intrinsic_span (P : Sylow 2 H) (J : Subgroup H)
    (hJ : J.IsCComponent) (hgen : J ⊔ (P : Subgroup H) = ⊤) :
    pResidual 2 H = conjugateSpanBy J ⊤ := by
  let := hJ.perfect
  have hp : IsPPerfect 2 J := by
    intro N hn hq
    let := hn
    let : Group.IsNilpotent (J ⧸ N) := hq.isNilpotent
    exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ N)
  apply le_antisymm
  · rw [pResidual_eq_iSup_conjugates J (P : Subgroup H) hp P.isPGroup' hgen,
      ← conjugateSpanBy_eq_iSup_conj]
    exact conjugateSpanBy_mono le_rfl le_top
  · exact conjugateSpanBy_le (le_pResidual_of_isPPerfect J hp)
      (by rw [normalizer_eq_top])

/-- Transport the E.2.2 component through the original inclusion H ↪ G,
including its own two-core quotient and the exact residual span. -/
theorem componentSeed_of_intrinsic (hTH : (T : Subgroup G) ≤ H)
    (J : Subgroup H) (hJ : J.IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J))
    (hgen : J ⊔ (T.subtype hTH : Subgroup H) = ⊤) :
    ComponentSeed T H (J.map H.subtype) := by
  have hc : Source.ComponentIn H (J.map H.subtype) := by
    refine ⟨map_subtype_le _, ?_⟩
    simpa only [subgroupOf, comap_map_eq_self_of_injective H.subtype_injective] using hJ
  refine ⟨hc, ?_, ?_, ?_⟩
  · let := hq
    let e : J ≃* J.map H.subtype := equivMapOfInjective J H.subtype H.subtype_injective
    exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  · have hh := congrArg (map H.subtype) hgen
    simpa only [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH,
      ← MonoidHom.range_eq_map, range_subtype] using hh
  · have hh := congrArg (map H.subtype) (intrinsic_span (T.subtype hTH) J hJ hgen)
    rw [map_conjugateSpanBy] at hh
    rw [Source.conjugateSpan, ← conjugateSpanBy_eq_iSup_conj]
    simpa only [residual, ← MonoidHom.range_eq_map, range_subtype] using hh

/-- Construct a component from the actual 11.3.2 counterexample; no
component, model, or normality witness is supplied by the caller. -/
theorem exists_componentSeed (h : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary) :
    ∃ K : Subgroup G, ComponentSeed T H K := by
  obtain ⟨J,hJ,hq,hgen,_⟩ := ChapterE.Structure.source_original_component
    (outside_sqtk h) (T.subtype h.outside.1.1.2)
    (outside_minimalParabolic h (weakClosure_not_le_core_of_counterexample h p hc))
    (counterexample_not_solvable h p hc hs)
  exact ⟨J.map H.subtype, componentSeed_of_intrinsic h.outside.1.1.2 J hJ hq hgen⟩

variable {K : Subgroup G}

omit [Finite G] in
/-- The constructed component lies in the literal ambient two-residual. -/
theorem ComponentSeed.le_residual (s : ComponentSeed T H K) : K ≤ residual H := by
  rw [s.span, Source.conjugateSpan, ← conjugateSpanBy_eq_iSup_conj]
  exact le_conjugateSpanBy _ _

/-- Since T normalizes L, the component generating H with T escapes N_G(L). -/
theorem ComponentSeed.outside (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) : ¬ K ≤ normalizer (L : Set G) := by
  intro hk
  apply h.outside.1.2
  rw [← s.supplement]
  exact sup_le hk D.sylow_normalizes_component

/-- All three clauses of the source local-component family hold. -/
theorem ComponentSeed.mem_local_family (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) : K ∈ Chapter1.L G (T : Subgroup G) := by
  change (K.subgroupOf (K ⊔ (T : Subgroup G))).IsCComponent ∧ _
  rw [s.supplement]
  refine ⟨s.component.2, ⟨T.subtype h.outside.1.1.2, ?_⟩, h.outside.1.1.1⟩
  exact map_subgroupOf_eq_of_le h.outside.1.1.2

/-- Movement of the original omega-center already occurs in this component. -/
theorem ComponentSeed.moves_omega_center (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) : ⁅sourceZ T, K⁆ ≠ ⊥ := by
  intro he
  apply h.moves_omega_center
  have hCK : K ≤ centralizer (sourceZ T : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
  have hCT : (T : Subgroup G) ≤ centralizer (sourceZ T : Set G) := by
    apply le_centralizer_iff.mp
    intro z hz
    exact ((mem_omegaCenterIn_iff _ _).mp hz).2.1
  have hCH : H ≤ centralizer (sourceZ T : Set G) := by
    rw [← s.supplement]
    exact sup_le hCK hCT
  have hz := commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hCH)
  simpa only [sourceZ, omegaCenterIn_eq_omegaOneAmbient] using hz

omit [Finite G] in
/-- The paired-case argument needs relative normality in H, not in G. -/
theorem ComponentSeed.normal_iff_eq_residual (s : ComponentSeed T H K) :
    (K.subgroupOf H).Normal ↔ K = residual H := by
  constructor
  · intro hn
    apply le_antisymm s.le_residual
    rw [s.span, Source.conjugateSpan, ← conjugateSpanBy_eq_iSup_conj]
    exact conjugateSpanBy_le le_rfl
      ((normal_subgroupOf_iff_le_normalizer s.component.1).mp hn)
  · intro he
    rw [he]
    exact residual_normal H

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
