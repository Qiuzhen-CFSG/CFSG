module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.Selection
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.ThreeStructure

/-!+# Applying 13.6.25–26 in the terminal component argument

The initial selection in 13.6.27 now receives n(H)>1 from the actual A₅
module calculation and E.3.35. For a Suzuki component, relative C(H)
membership is transported along H's inclusion before applying 13.6.26(1);
13.6.25(3) supplies the solvable Borel containment in the existing join
construction. The resulting join also has generation parameter above one.

Finally, applying the original quotient map to O_{2,p}(H)=Q_H gives
O_p(H/O₂(H))=1 for p>3. This discharges the large-prime premise of the
terminal component-structure theorem on the literal involution centralizer
and restricted Sylow. Its candidate, uniqueness and quasisimplicity inputs
belong to the subsequent 13.6.27 argument, owned by
`qt-13-06-terminal-contradiction`; they are not claims of this module.

The earlier source owners are listed in `SourceParameters`. No numerical
module premise, solvable-overgroup conclusion, component-exclusion premise
or large-prime core conclusion remains an input to these applications.
Legacy `Parameters`, `TerminalContradiction`, and sibling modules are preserved.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.6.25–27, printed pp.934–935.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters

open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V M MV : Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] in
private theorem marked_involution_order (s : EarlierA5Setup T L V M MV) :
    orderOf s.z.val = 2 :=
  orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian s.z.val s.z.property)
    (fun h => s.z_nonidentity (Subtype.ext h))

/-- The original quotient map turns the proved iterated-core equality into
the large-prime exclusion required by the terminal Fitting calculation. -/
theorem quotient_pCore_eq_bot_of_source (s : EarlierA5Setup T L V M MV)
    (he : EarlierE335 (G := G)) (h1338 : Earlier1338Two T)
    (L₁ G₁ : Subgroup G) {H : Subgroup G}
    (hH : H ∈ Chapter13.Section08.Source.Hz L₁ (T : Subgroup G) G₁ M)
    (p : ℕ) (hp : p.Prime) (hlarge : 3 < p) :
    pCore p (H ⧸ pCore 2 H) = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  have h := source_13_6_26_2_from_generators s s.localA_eq_one he h1338 L₁ G₁ hH p hlarge
  have hi : twoPCore p H = pCore 2 H := map_injective H.subtype_injective h
  have hm := congrArg (map (QuotientGroup.mk' (pCore 2 H))) hi
  simpa only [twoPCore, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
    QuotientGroup.map_mk'_self] using hm

/-- The intrinsic component convention used by the terminal Suzuki proof
is exactly relative C(H), after mapping through H's original inclusion. -/
theorem component_image_not_le_of_source (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hA38 : EarlierA38Three.{u}) (s : EarlierA5Setup T L V M MV)
    (L₁ G₁ : Subgroup G) {H : Subgroup G}
    (hH : H ∈ Chapter13.Section08.Source.Hz L₁ (T : Subgroup G) G₁ M)
    (K : Subgroup H) (hK : K.IsCComponent) : ¬ K.map H.subtype ≤ M := by
  apply source_13_6_26_1_of_A5_setup hG hA38 T L V M MV L₁ G₁ s hH
  refine ⟨map_subtype_le K, ?_⟩
  change (Subgroup.comap H.subtype (K.map H.subtype)).IsCComponent
  rwa [comap_map_eq_self_of_injective H.subtype_injective]

/-- The first construction of 13.6.27, with its complete 13.6.25(2)
premise discharged. The earlier centrality of z in T is retained. -/
theorem exists_initial_residual_of_source (s : EarlierA5Setup T L V M MV)
    (he : EarlierE335 (G := G))
    (hT : (T : Subgroup G) ≤ centralizer ({s.z.val} : Set G)) :
    ∃ H ∈ Chapter3.HStar (T : Subgroup G) M,
      H ≤ centralizer ({s.z.val} : Set G) ∧
      1 < ChapterE.generationParameter H ∧
      (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H ∧
      ¬ (pResidual 2 H).map H.subtype ≤ M ∧
      (T : Subgroup G) ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) := by
  have hM : M ∈ maximalTwoLocalOvergroups (L ⊔ (T : Subgroup G)) :=
    s.unique_overgroup.symm ▸ Set.mem_singleton M
  exact Components.exists_initial_residual T M s.z.val (marked_involution_order s)
    hT (le_sup_right.trans hM.2) s.singular_escape (source_13_6_25 s he).2.1

/-- The actual Suzuki join used in 13.6.27, with the solvable containment,
relative component exclusion and generation bound all supplied by 13.6.25–26.
The later model identification and normalization remain with the component owner. -/
theorem suzuki_join_mem_HStar_of_source (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hA38 : EarlierA38Three.{u}) (s : EarlierA5Setup T L V M MV)
    (he : EarlierE335 (G := G)) (L₁ : Subgroup G) {H : Subgroup G}
    (hH : H ∈ Chapter13.Section08.Source.Hz L₁ (T : Subgroup G)
      (centralizer ({s.z.val} : Set G)) M)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hn : (T : Subgroup G).subgroupOf H ≤ normalizer (K : Set H))
    {m : ℕ} (e : (K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    K.map H.subtype ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) M ∧
      1 < ChapterE.generationParameter (K.map H.subtype ⊔ (T : Subgroup G) : Subgroup G) := by
  have h25 := source_13_6_25 s he
  have hJ := Components.SuzukiIsolation.hz_component_join_mem_HStar T L₁ H M s.z.val
    (marked_involution_order s) (s.module_le s.z.property) hH K hK hn e h25.2.2.1
    (fun J hJ D hD => component_image_not_le_of_source hG hA38 s L₁ _ hJ D hD)
  have hmin : Minimal (fun J => J ∈ Chapter1.HOver G (T : Set G) ∧ ¬ J ≤ M)
      (K.map H.subtype ⊔ (T : Subgroup G)) := hJ
  exact ⟨hJ, h25.2.1 _ hmin.prop⟩

/-- The literal terminal component conclusion, with the large-prime core
premise of `conclusion_of_candidate` discharged by source 13.6.26(2).
Candidate construction and uniqueness are the independent 13.6.27 branches. -/
theorem terminal_component_conclusion_of_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (s : EarlierA5Setup T L V M MV) (he : EarlierE335 (G := G))
    (h1338 : Earlier1338Two T) (L₁ : Subgroup G)
    (hH : centralizer ({s.z.val} : Set G) ∈ Chapter13.Section08.Source.Hz
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
    (hG.involution_centralizer_sqtk (marked_involution_order s)) (T.subtype hTH) hK hc hu
    (fun p hp hlarge => quotient_pCore_eq_bot_of_source s he h1338 L₁ _ hH p hp hlarge)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters
