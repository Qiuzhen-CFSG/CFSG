module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.RelativeComponents.SourceOrbit
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.KnownSimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.SourceKernel
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.Complete
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SourceB5.Quasisimple

/-!
# The original A₅ setup in the terminal argument

The source orbit theorem and solvable-overgroup theorem give the large-prime
core exclusion on the literal two-core quotient. This supplies the final
Fitting calculation of 13.6.27 without a universal E.3.35 or A.3.8 premise.
The completed B.4.2 theorem is applied to the same faithful representation
and best offender used by the terminal ratio argument.

The marked setup supplies the five-coordinate action, fusion, abelian closure,
and both centralizer conditions. The component candidate and uniqueness,
13.3.8(2), the earlier 13.5.7 family, F.9.16(3), and B.4.5 remain explicit
where they are used. In particular these are assembly lemmas, not a proof of
Theorem 13.6.1: its original setup and remaining source conclusions must still
be constructed by the Section 13.6 owner.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
13.6.25--27 and the final paragraph, printed pp.934--935; B.4.2, p.86.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
universe u v

/-- The corrected full B.4.2 input is supplied by the proved known-simple
classification, retaining the actual representation and best offender. -/
theorem terminal_fullB42_knownSimple :
    Ratio.SourceClassifications.FullB42.{u,v} KnownSimple.IsKnownSimple := by
  intro D _ _ W _ _ _ ρ A h
  apply Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.SourceB5.irreducible
  exact ChapterB.SourceClassification.actionCase_of_bestOffender
    h.sqtk rfl h.quasisimple h.faithful h.irreducible h.bestOffender

namespace SourceParameters
variable {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V M MV : Subgroup G} [IsElementaryAbelian 2 V]

/-- Project the original iterated-core equality through H's own two-core
quotient. No universal generation-parameter implication is assumed. -/
theorem quotient_pCore_eq_bot_of_original_setup
    (s : EarlierA5Setup T L V M MV) (h1338 : Earlier1338Two T)
    (L₁ G₁ : Subgroup G) {H : Subgroup G}
    (hH : H ∈ Section08.Source.Hz L₁ (T : Subgroup G) G₁ M)
    (p : ℕ) (hp : p.Prime) (hlarge : 3 < p) :
    pCore p (H ⧸ pCore 2 H) = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  have h := source_13_6_26_2_of_solvable_source s s.localA_eq_one h1338 L₁ G₁ hH p hlarge
  have hi : twoPCore p H = pCore 2 H := map_injective H.subtype_injective h
  have hm := congrArg (map (QuotientGroup.mk' (pCore 2 H))) hi
  simpa only [twoPCore, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
    QuotientGroup.map_mk'_self] using hm

omit [Finite G] in
/-- The marked nonidentity binary vector is the actual ambient involution. -/
theorem EarlierA5Setup.marked_order (s : EarlierA5Setup T L V M MV) :
    orderOf s.z.val = 2 :=
  orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian s.z.val s.z.property)
    (fun h => s.z_nonidentity (Subtype.ext h))

/-- The remaining candidate and uniqueness proofs feed the literal
13.6.27 endgame with all large-prime core premises discharged. -/
theorem terminal_component_conclusion_of_original_setup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (s : EarlierA5Setup T L V M MV) (h1338 : Earlier1338Two T)
    (L₁ : Subgroup G)
    (hH : centralizer ({s.z.val} : Set G) ∈ Section08.Source.Hz
      L₁ (T : Subgroup G) (centralizer ({s.z.val} : Set G)) M)
    {K : Subgroup (centralizer ({s.z.val} : Set G))} (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    (hc : Components.Candidate ((T : Subgroup G).subgroupOf
      (centralizer ({s.z.val} : Set G))) K)
    (hu : ∀ D : Subgroup (centralizer ({s.z.val} : Set G)), D.IsCComponent → D = K) :
    Components.Conclusion ((T : Subgroup G).subgroupOf (centralizer ({s.z.val} : Set G))) := by
  have hTH : (T : Subgroup G) ≤ centralizer ({s.z.val} : Set G) :=
    le_sup_right.trans hH.1.2
  exact Components.ThreeStructure.conclusion_of_candidate
    (hG.involution_centralizer_sqtk s.marked_order) (T.subtype hTH) hK hc hu
    (fun p hp hlarge => quotient_pCore_eq_bot_of_original_setup s h1338 L₁ _ hH p hp hlarge)

/-- Relative C(H) membership is transported through H's actual inclusion.
The proved source orbit theorem discharges the old A.3.8 callback. -/
theorem component_image_not_le_of_original_setup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (s : EarlierA5Setup T L V M MV) (L₁ G₁ : Subgroup G)
    {H : Subgroup G} (hH : H ∈ Section08.Source.Hz L₁ (T : Subgroup G) G₁ M)
    (K : Subgroup H) (hK : K.IsCComponent) : ¬ K.map H.subtype ≤ M := by
  apply source_13_6_26_1_of_A5_source hG T L V M MV L₁ G₁ s hH
  refine ⟨map_subtype_le K, ?_⟩
  change (Subgroup.comap H.subtype (K.map H.subtype)).IsCComponent
  rwa [comap_map_eq_self_of_injective H.subtype_injective]

/-- The original Suzuki join receives both the source component exclusion
and the proved generation bound on every overgroup outside M. -/
theorem suzuki_join_mem_HStar_of_original_setup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (s : EarlierA5Setup T L V M MV) (L₁ : Subgroup G) {H : Subgroup G}
    (hH : H ∈ Section08.Source.Hz L₁ (T : Subgroup G)
      (centralizer ({s.z.val} : Set G)) M)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hn : (T : Subgroup G).subgroupOf H ≤ normalizer (K : Set H))
    {m : ℕ} (e : (K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    K.map H.subtype ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) M ∧
      1 < ChapterE.generationParameter (K.map H.subtype ⊔ (T : Subgroup G) : Subgroup G) := by
  have h25 := source_13_6_25_knownSimple hG s
  have hJ := Components.SuzukiIsolation.hz_component_join_mem_HStar T L₁ H M s.z.val
    s.marked_order (s.module_le s.z.property) hH K hK hn e h25.2.2.1
    (fun J hJ D hD => component_image_not_le_of_original_setup hG s L₁ _ hJ D hD)
  have hmin : Minimal (fun J => J ∈ Chapter1.HOver G (T : Set G) ∧ ¬ J ≤ M)
      (K.map H.subtype ⊔ (T : Subgroup G)) := hJ
  exact ⟨hJ, h25.2.1 _ hmin.prop⟩

/-- Apply the terminal ratio contradiction to the original A₅ setup.
The F.9 kernel and B.4.2 are proved here; the component conclusion,
13.5.7, F.9.16(3), and B.4.5 retain their explicit source obligations. -/
theorem terminal_contradiction_of_original_setup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (s : EarlierA5Setup T L V M MV) (V₃ : Subgroup G)
    (hT : (T : Subgroup G) ≤ centralizer ({s.z.val} : Set G))
    (hmark : ∀ x : V, x.val ∈ V₃ ↔ (s.coordinates.equiv x).toAdd.val 4 = 0)
    (hN : normalizer (V₃ : Set G) ≤ normalizer (V : Set G))
    (hcomponents : Components.Conclusion
      ((T : Subgroup G).subgroupOf (centralizer ({s.z.val} : Set G))))
    (h1357 : Ratio.Earlier1357 T L V V₃ (zpowers s.z.val)
      (centralizer ({s.z.val} : Set G)) M)
    (hF9163 : Ratio.EarlierF9163 T L V V₃ (zpowers s.z.val))
    (hB45 : Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource.FullB45.{u,u}
      KnownSimple.IsKnownSimple) : False := by
  let := s.abelian_closure
  have hcontains : Ratio.residualCentralizer L (zpowers s.z.val) ⊔ (T : Subgroup G) ≤
      centralizer ({s.z.val} : Set G) := by
    refine sup_le ?_ hT
    exact (map_subtype_le _).trans (inf_le_right.trans
      (centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers s.z.val))))
  exact Ratio.terminal_contradiction_of_source_kernel hG s.coordinates s.v s.z
    s.nonsingular s.z_nonidentity s.marked_order s.singular s.alternating_le_actor s.fusion
    (s.module_normalizer ▸ s.nonsingular_centralizer) hmark hN hcontains
    s.singular_escape hcomponents h1357 hF9163 terminal_fullB42_knownSimple hB45

end SourceParameters
end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
