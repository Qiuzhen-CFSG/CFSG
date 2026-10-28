module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ParameterSetup
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.ResidualFive

/-!
# The complete original A₅ parameter and prime-core deductions

The literal original context constructs the marked source setup. The direct
A₅ quotient-action proof then kills the prime-to-p residual of O_{2,p}(H)
for p > 3. Together with the proved component-orbit argument, this supplies
both clauses of 13.6.26 on every original H_z member. In particular the
component extension uses the original quotient map with no universal
13.3.8 premise.

The original nonsingular centralizer bound, singular escape, model exclusions
and earlier full A.3.12 statement are retained. The component conclusion
still requires the genuine exceptional candidate and uniqueness inputs.
Source: Aschbacher–Smith 13.6.26–27, printed pp.934–935.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source SourceParameters
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G} [IsElementaryAbelian 2 V]

/-- Both source clauses of 13.6.26 on the original H_z family. The A₅
quotient action excludes the large-prime residual directly. -/
theorem source_13_6_26_of_context
    (d : Context T L V V₁ V₂ V₃)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ →
      ∀ (S : Sylow 2 Y) (B : Subgroup Y), B ∈ ChapterA.Section03.localCComponents S →
        Chapter1.Section02.A312Conclusion B)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G) (L₁ G₁ : Subgroup G)
    {H : Subgroup G}
    (hH : H ∈ Section08.Source.Hz L₁ (T : Subgroup G) G₁ (normalizer (L : Set G))) :
    (∀ K ∈ Chapter1.cComponentsIn H, ¬ K ≤ normalizer (L : Set G)) ∧
      ∀ p : ℕ, p.Prime → 3 < p → O2p H p = Section08.Source.QH H := by
  obtain ⟨s, _, _⟩ := source_parameter_setup d hA312 hCv houtside hcounter
  refine ⟨source_13_6_26_1_of_A5_source d.hypothesis.qtke T L V _ _ L₁ G₁ s hH, ?_⟩
  intro p hp hlarge
  let : Fact p.Prime := ⟨hp⟩
  exact source_13_6_26_2_of_A5_setup d.hypothesis.qtke s L₁ G₁ hH p hlarge

/-- The literal quotient-core conclusion used by the final component
extension, without a universal 13.3.8 input. -/
theorem source_quotient_pCore_eq_bot_of_context_native
    (d : Context T L V V₁ V₂ V₃)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ →
      ∀ (S : Sylow 2 Y) (B : Subgroup Y), B ∈ ChapterA.Section03.localCComponents S →
        Chapter1.Section02.A312Conclusion B)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G) (L₁ G₁ : Subgroup G)
    {H : Subgroup G}
    (hH : H ∈ Section08.Source.Hz L₁ (T : Subgroup G) G₁ (normalizer (L : Set G)))
    (p : ℕ) (hp : p.Prime) (hlarge : 3 < p) :
    pCore p (H ⧸ pCore 2 H) = ⊥ := by
  have h := (source_13_6_26_of_context d hA312 hCv houtside hcounter L₁ G₁ hH).2 p hp hlarge
  have hi : twoPCore p H = pCore 2 H := map_injective H.subtype_injective h
  have hm := congrArg (map (QuotientGroup.mk' (pCore 2 H))) hi
  simpa only [twoPCore, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
    QuotientGroup.map_mk'_self] using hm

/-- The component extension from the exact candidate and uniqueness, with
all source prime-core and generation premises discharged. -/
theorem source_component_conclusion_of_context_native
    (d : Context T L V V₁ V₂ V₃)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ →
      ∀ (S : Sylow 2 Y) (B : Subgroup Y), B ∈ ChapterA.Section03.localCComponents S →
        Chapter1.Section02.A312Conclusion B)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    {K : Subgroup (centralizer (V₁ : Set G))} (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hc : Components.Candidate ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) K)
    (hu : ∀ D : Subgroup (centralizer (V₁ : Set G)), D.IsCComponent → D = K) :
    Components.Conclusion ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) := by
  have hH := SourceAbelian.point_centralizer_mem_family d houtside
  have hT : (T : Subgroup G) ≤ centralizer (V₁ : Set G) :=
    d.flag.one_invariant.trans (normalizer_le_centralizer_of_card_two V₁ d.flag.one_card)
  exact Components.ThreeStructure.conclusion_of_candidate
    (Chapter1.RadicalExclusions.sqtk_of_mem_H d.hypothesis.qtke hH.1.1)
    (T.subtype hT) hK hc hu
    (fun p hp hlarge => source_quotient_pCore_eq_bot_of_context_native d hA312 hCv
      houtside hcounter (Ratio.residualCentralizer L V₁) _ hH p hp hlarge)


end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
