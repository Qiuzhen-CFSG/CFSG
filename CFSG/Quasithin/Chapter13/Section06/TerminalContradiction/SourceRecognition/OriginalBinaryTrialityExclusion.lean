module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ContextKnownSimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ResidualKnownSimple
public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.NormalTrialityActor
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Offenders.PrimeCoreAction
public import Theory.SpecificGroups.Triality.BinaryCenter

/-!
# No normal binary triality component in the original singular centralizer

For an actual normal component X of C_G(V₁), form X L₁ T. The original
13.5.7 and F.9.16 arguments apply to this member of H_z and produce a
quadratic actor in its edge two-core. Since X and the edge generate this
group, the actor has trivial intersection with the centralizer of X modulo
the two-core. The surviving triality section therefore retains its rank
and its fixed-codimension bound, contradicting the triality source theorem.

No exceptional candidate, generalized-Fitting identity, or ratio bound on
an arbitrarily restricted action is assumed.
Source: Aschbacher--Smith 13.6.26--27, p.934--935; F.9.16--18, p.324--325.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open Ratio Section05.A5Source CentralizerReduction CentralizerReduction.A5Module Section08
open Section08.SolvableExclusion.Three
open Section08.SolvableExclusion.Three.Supercritical.Offenders
universe u
variable {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- A normal C-component of the original point centralizer cannot have
the genuine binary triality quotient. All source actor data are constructed. -/
theorem original_normal_binary_triality_point_component_false
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    (X : Subgroup G) (hXC : X ≤ centralizer (V₁ : Set G))
    (hX : (X.subgroupOf (centralizer (V₁ : Set G))).IsCComponent)
    (hXn : (X.subgroupOf (centralizer (V₁ : Set G))).Normal)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (X ⧸ pCore 2 X)) : False := by
  let := d.elementary
  let C := centralizer (V₁ : Set G)
  let L₁ := residualCentralizer L V₁
  let H := X ⊔ (L₁ ⊔ (T : Subgroup G))
  let J := (L ⊔ (T : Subgroup G)) ⊓ H
  have hC : C ∈ Source.Hz L₁ (T : Subgroup G) C (normalizer (L : Set G)) :=
    SourceAbelian.point_centralizer_mem_family d houtside
  have hXM : ¬ X ≤ normalizer (L : Set G) :=
    (source_13_6_26_of_context_knownSimple d hCv houtside hcounter L₁ C hC).1 X ⟨hXC,hX⟩
  have hHC : H ≤ C := sup_le hXC hC.1.2
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans le_sup_right
  have hVH : V₁ ≤ H :=
    (d.flag.one_le_two.trans (d.flag.two_le_V.trans d.flag.V_le_T)).trans hTH
  have hHN : H ≤ normalizer (V₁ : Set G) := hHC.trans (Subgroup.centralizer_le_normalizer _)
  have hVHcore : V₁ ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes
    (T.isPGroup'.to_le (d.flag.one_le_two.trans (d.flag.two_le_V.trans d.flag.V_le_T)))
    hVH hHN
  have hH : H ∈ Source.Hz L₁ (T : Subgroup G) C (normalizer (L : Set G)) := by
    refine ⟨⟨?_,show L₁ ⊔ (T : Subgroup G) ≤ H from le_sup_right⟩,
      hHC,fun hh => hXM (le_sup_left.trans hh)⟩
    intro hz
    have hv : V₁ = ⊥ := bot_unique (hVHcore.trans_eq hz)
    have hc := d.flag.one_card
    rw [hv,card_bot] at hc
    omega
  have hXH : X ≤ H := le_sup_left
  have hXHc : (X.subgroupOf H).IsCComponent := hX.subgroupOf_of_le hXH hHC
  have hCN : C ≤ normalizer (X : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hXC).mp hXn
  let : (X.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hXH).mpr (hHC.trans hCN)
  have hgen : X ⊔ J = H := by
    apply le_antisymm (sup_le hXH inf_le_right)
    apply sup_le le_sup_left
    apply le_trans _ le_sup_right
    apply le_inf _ le_sup_right
    apply sup_le _ le_sup_right
    exact (map_subtype_le _ |>.trans inf_le_left).trans le_sup_left
  obtain ⟨c,hv,_⟩ := source_coordinates d
  have hpoint : centralizer ({c.singular.val} : Set G) = C := by
    calc
      _ = centralizer (zpowers c.singular.val : Set G) := by
        rw [zpowers_eq_closure,centralizer_closure]
      _ = _ := congrArg (fun W : Subgroup G => centralizer (W : Set G)) c.line_eq
  let := SourceAbelian.source_closure_abelian_knownSimple d c.singular.val c.line_eq
    (by change ¬ centralizer ({c.singular.val} : Set G) ≤ _; rwa [hpoint]) hcounter
  let : IsMulCommutative (conjugateSpanBy V C) := by
    rw [←hpoint,←centralizerConjugateClosure_eq_conjugateSpanBy]
    infer_instance
  let : IsMulCommutative (conjugateSpanBy V H) :=
    conjugateSpanBy_isMulCommutative_of_le le_rfl hHC
  let : IsElementaryAbelian 2 (conjugateSpanBy V H) :=
    conjugateSpanBy_elementary_of_commutative V H
  have h91 : SourceF91 T L V V₃ V₁ H := source13_5_7_knownSimple d hH
  let hU : IsElementaryAbelian 2 (Source.UH H V₃) :=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono h91.v₃_le le_rfl)
  let := hU
  have hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H :=
    earlierF923_of_source T L V V₃ V₁ H h91
  have hcv : centralizer ({c.nonsingular.val} : Set G) ≤ normalizer (V : Set G) := by
    simpa only [hv] using hCv
  have hfusion := d.flag.normalizer_controls_fusion_of_nonsingular_centralizer hCv
  have h91z : SourceF91 T L V V₃ (zpowers c.singular.val) H := c.line_eq.symm ▸ h91
  have h98z := sourceF98_of_five c.coordinates c.nonsingular c.singular
    c.form_nonsingular c.singular_ne_one c.form_singular c.alternating_le hfusion hcv
    c.third_mark d.seed_normalizer_knownSimple h91z
  have h98 : SourceF98 T L V V₃ V₁ H := c.line_eq ▸ h98z
  have hF : EarlierF9163 T L V V₃ V₁ := c.line_eq ▸
    earlierF9163_of_five c.coordinates c.nonsingular c.singular c.form_nonsingular
      c.singular_ne_one c.form_singular c.alternating_le hfusion hcv c.third_mark
      d.seed_normalizer_knownSimple
  obtain ⟨B,hB,hBe,hBq,hBc⟩ := hF H hU h98 hHN hk
  let q := QuotientGroup.mk' (pCore 2 H)
  let K := Source.starImage H X
  let A := B.map q
  let ρ := starRepresentation H V₃ V₁ hHN hk
  let : K.Normal := (inferInstance : (X.subgroupOf H).Normal).map q
    (QuotientGroup.mk'_surjective _)
  have hstar : K ⊔ Source.starImage H J = ⊤ := by
    unfold K Source.starImage
    rw [←Subgroup.map_sup,←subgroupOf_sup hXH inf_le_right,hgen,subgroupOf_self,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hfaithCore : Source.starImage H (J.pCoreIn 2) ⊓ centralizer (K : Set (Source.Hstar H)) = ⊥ :=
    centralizer_inf_eq_bot_of_supplement K (Source.starImage H J)
      (Source.starImage H (J.pCoreIn 2)) hstar
      (starImage_isPGroup H _ (isPGroup_pCoreIn 2 J))
      (starImage_normalizes H (le_normalizer_pCoreIn 2 J)) (hstar_twoCore H)
  have hAC : A ⊓ centralizer (K : Set (Source.Hstar H)) = ⊥ :=
    bot_unique ((inf_le_inf_right _ (map_mono hB)).trans_eq hfaithCore)
  let eX := subgroupOfEquivOfLe hXH
  let eQ := QuotientGroup.congr _ _ eX (pCore_map_iso 2 eX)
  have hmK : Triality.Standard.IsTrialityGroupAt 2 K :=
    hm.of_mulEquiv ((cComponentTwoCoreQuotientEquiv hXHc).symm.trans eQ)
  obtain ⟨eK⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff K 1 Nat.zero_lt_one).mp
    (by simpa using hmK)
  have hZ : center K = ⊥ := by
    apply map_injective (f := eK.toMonoidHom) eK.injective
    rw [map_center_equiv,Subgroup.map_bot,Triality.Standard.binaryCarrier_center_eq_bot]
  let : IsSimpleGroup K := eK.isSimpleGroup
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := eK.symm.toMonoidHom) eK.symm.surjective
  let : IsQuasisimple K :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hsH : IsSQTK KnownSimple.IsKnownSimple H :=
    Chapter1.RadicalExclusions.sqtk_of_mem_H d.hypothesis.qtke hH.1.1
  have hs : IsSQTK KnownSimple.IsKnownSimple (Source.Hstar H) := by
    refine ⟨?_,hsH.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 H) pCore_isPGroup).trans
      (hsH.stronglyQuasithin p hp ho)
  exact ChapterB.SmallRatioClassification.triality_excluded_of_faithful_quadratic_actor
    ρ K A hZ hs (starRepresentation_injective H V₃ V₁ hHN hk) (n := 1) (by decide)
    (by simpa using (hmK.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)))
    hBe hBq hBc hAC

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
