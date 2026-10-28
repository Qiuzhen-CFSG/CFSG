module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.ModelDispatch
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.HeldAmbient
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.SourceReduction
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.CentralCover
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SourceBalance
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs
public import CFSG.Quasithin.ChapterI.Section03.RankTwoSource.EarlierSources
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SourceSevenEscape
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.Reduction
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.CommonNormalKnownSimple

/-!
# The original E.6.18 assembly with concrete model prerequisites

I.3.1 constructs a containing component normal in C_G(A), with A the actual
nonidentity intersection. The original subgroup is transported through each
centralizer subtype. The complete Theorems A and C provide the literal
central-quotient model; GLS orbit/projection is instantiated internally.
All ordinary cases use the concrete model dispatch and faithful central-cover
action. Held instead uses the proved ambient Sylow argument at the original
corank bound. The result is precisely SevenExcluded used by E.6.19 onward.

The original A.3.6/A.3.8, escape and common-normal inputs are instantiated
in the final known-simple wrapper. This remains conditional on the remaining
concrete model facts and the genuine Held odd center.
It is not a claim that those source prerequisites have been completed. No unrestricted
Held inspection, induced-action conclusion, or Sylow condition is assumed.

Source: Aschbacher–Smith, E.6.18, printed p.252; I.3.1(3), pp.414–415.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
open ChapterI.RankTwoSource
universe u
variable {G : Type u} [Group G] [Finite G] {M V A U L : Subgroup G}

omit [Finite G] in
private theorem centralizerComponent_subgroupOf {U L H : Subgroup G} (hUH : U ≤ H)
    (hCH : centralizer (U : Set G) ≤ H) (hL : CentralizerComponent U L) :
    CentralizerComponent (U.subgroupOf H) (L.subgroupOf H) := by
  let P := U.subgroupOf H
  let C := centralizer (P : Set H)
  let D := centralizer (U : Set G)
  let e : C ≃* D :=
    { toFun := fun x => ⟨x.val.val, by
        intro u hu
        exact congrArg Subtype.val (x.property ⟨u, hUH hu⟩ hu)⟩
      invFun := fun x => ⟨⟨x.val, hCH x.property⟩, by
        intro u hu
        exact Subtype.ext (x.property u hu)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have he : (L.subgroupOf D).map e.symm.toMonoidHom = (L.subgroupOf H).subgroupOf C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
  refine ⟨?_, he ▸ hL.2.map_equiv e.symm⟩
  intro l hl p hp
  exact Subtype.ext (hL.1 hl p hp)


private theorem original_normal_component
    (hA36 : EarlierA36.{u} KnownSimple.IsKnownSimple)
    (hA38 : EarlierA38.{u} KnownSimple.IsKnownSimple)
    {T : Sylow 2 G} (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (hAU : A ≤ U) (hUV : U ≤ V) (hA : A ≠ ⊥)
    (hL : CentralizerComponent U L) (hs : IsSeven L) :
    ∃ J : Subgroup G, L ≤ J ∧ IsComponentIn J (centralizer (A : Set G)) ∧
      (J.subgroupOf (centralizer (A : Set G))).Normal := by
  let _ := h.elementary
  let H := centralizer (A : Set G)
  have hH := subspaceCentralizer_sqtk h (hAU.trans hUV) hA
  have hUH : U ≤ H := hUV.trans
    (V.le_centralizer.trans (Subgroup.centralizer_le (hAU.trans hUV)))
  have hCH : centralizer (U : Set G) ≤ H := Subgroup.centralizer_le hAU
  have hLH : L ≤ H := hL.1.trans hCH
  let P := U.subgroupOf H
  let D := L.subgroupOf H
  have hDP : CentralizerComponent P D := centralizerComponent_subgroupOf hUH hCH hL
  have hsD : IsSeven D := hs.of_equiv (subgroupOfEquivOfLe hLH).symm
  have hP : IsPGroup 2 P := ((IsElementaryAbelian.isPGroup 2 V).to_le hUV).of_equiv
    (subgroupOfEquivOfLe hUH).symm
  have hr : primeRank 3 D = 2 := le_antisymm
    ((Theory.GroupTheory.primeRank_le_of_injective 3 D.subtype D.subtype_injective).trans
      (hH.stronglyQuasithin 3 (by decide) (by decide))) hsD.two_le_primeRank
  obtain ⟨J,hDJ,hnJ,hJ⟩ := SourceBalance.normal_component_of_rank_two hA36 hA38
    (earlierOrbitProjection KnownSimple.IsKnownSimple) H hH P D hP hDP hr
  let Y := J.map H.subtype
  have hYH : Y ≤ H := map_subtype_le J
  have hY : Y.subgroupOf H = J := comap_map_eq_self (by simp)
  refine ⟨Y, ?_, ⟨hYH, ?_⟩, ?_⟩
  · rw [← map_subgroupOf_eq_of_le hLH]
    exact map_mono hDJ
  · rwa [hY]
  · rwa [hY]

private theorem quotient_source_model
    {X : Type u} [Group X] [Finite X] [IsQuasisimple X]
    (hX : IsSQTK KnownSimple.IsKnownSimple X) :
    IsStronglyQuasithin (X ⧸ center X) ∧
      Chapter1.Section02.LocalModels.TheoremCModel (X ⧸ center X) := by
  let Q := X ⧸ center X
  let : IsSimpleGroup Q := IsQuasisimple.simple
  let : IsQuasisimple Q := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center X)) (QuotientGroup.mk'_surjective (center X))
  have htop : IsComponent Q (⊤ : Subgroup Q) :=
    ⟨Subgroup.IsSubnormal.top, IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm⟩
  have hsemi : ChapterA.Section02.IsSemisimple Q := top_unique (le_sSup htop)
  have hsec : ChapterA.Section02.IsSectionOf Q X :=
    .of_surjective (QuotientGroup.mk' (center X)) (QuotientGroup.mk'_surjective (center X))
  have hqt : IsStronglyQuasithin Q := ChapterA.Section02.theoremA_knownSimple.stronglyQuasithin_section
    hX.stronglyQuasithin hX.isKGroup hsec hsemi
  have hna : ¬ IsMulCommutative Q := fun hc => by
    let := hc
    exact Group.IsPerfect.not_isSolvable Q inferInstance
  refine ⟨hqt, ChapterA.Section03.SourceComponents.sourceTheoremC_to_local hna ?_⟩
  exact ChapterA.Section02.theoremC_knownSimple inferInstance hna hqt
    (hX.isKGroup.quotient (center X))

omit [Finite G] in
private theorem relative_component_centralizes_of_inspection
    {J : Subgroup G} (hJA : J ≤ centralizer (A : Set G))
    (hn : (J.subgroupOf (centralizer (A : Set G))).Normal)
    (hAU : A ≤ U) (hUA : U ≤ centralizer (A : Set G))
    (hL : CentralizerComponent U L) (hLJ : L ≤ J) (hs : IsSeven L)
    (hp : IsPGroup 2 U) (hi : SevenActionInspection J) :
    J ≤ centralizer (U : Set G) := by
  let H := centralizer (A : Set G)
  let JH := J.subgroupOf H
  let P := U.subgroupOf H
  let D := L.subgroupOf H
  let : JH.Normal := hn
  have hD := centralizerComponent_subgroupOf hUA (Subgroup.centralizer_le hAU) hL
  have hiJ : SevenActionInspection JH :=
    SporadicInspection.of_equiv (subgroupOfEquivOfLe hJA) hi
  have hJC := hiJ.modelInspection JH P D
    (hp.of_equiv (subgroupOfEquivOfLe hUA).symm) hD (fun _ hx => hLJ hx)
    (hs.of_equiv (subgroupOfEquivOfLe (hLJ.trans hJA)).symm)
  intro j hj u hu
  exact congrArg Subtype.val (hJC (show (⟨j,hJA hj⟩ : H) ∈ JH from hj)
    ⟨u,hUA hu⟩ hu)

/-- Original corank-two lifting from the outstanding concrete fixed-group
facts and the genuine Held cover center. A/C and GLS orbit/projection are
instantiated internally; only the earlier A.3.6 and A.3.8 inputs remain. -/
theorem corank_two_lifting_of_model_facts
    (d : SevenInspectionModelFacts)
    (hHeld : ∀ (X : Type u) [Group X] [Finite X] [IsQuasisimple X],
      Nonempty ((X ⧸ center X) ≃* Held.He) → Odd (Nat.card (center X)))
    (hA36 : EarlierA36.{u} KnownSimple.IsKnownSimple)
    (hA38 : EarlierA38.{u} KnownSimple.IsKnownSimple)
    {T : Sylow 2 G} (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    [IsElementaryAbelian 2 V] (hm : 2 < localM V) : SevenCorankTwoLifting V := by
  intro A U L hAU hUV hA hc hL hs
  obtain ⟨J,hLJ,hJ,hn⟩ := original_normal_component hA36 hA38 h hAU hUV hA hL hs
  let : IsQuasisimple J := hJ.quasisimple
  let H := centralizer (A : Set G)
  have hJH : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJ.1)).mp
      ((subspaceCentralizer_sqtk h (hAU.trans hUV) hA).subgroup (J.subgroupOf H))
  obtain ⟨hqt,hmodel⟩ := quotient_source_model hJH
  let : IsSimpleGroup (J ⧸ center J) := IsQuasisimple.simple
  let : IsQuasisimple (J ⧸ center J) := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center J)) (QuotientGroup.mk'_surjective _)
  have hna : ¬ IsMulCommutative (J ⧸ center J) := fun hcom => by
    let := hcom
    exact Group.IsPerfect.not_isSolvable (J ⧸ center J) inferInstance
  rcases inspection_or_held_of_model_facts d hna hqt hmodel with hi | he
  · have hJU := relative_component_centralizes_of_inspection hJ.1 hn hAU
      (hUV.trans (V.le_centralizer.trans (Subgroup.centralizer_le (hAU.trans hUV))))
      hL hLJ hs ((IsElementaryAbelian.isPGroup 2 V).to_le hUV)
      (sevenActionInspection_of_quotient_center hi)
    have hJC := hJ.restrict hJU (Subgroup.centralizer_le hAU)
    have heq := hL.2.eq_of_le hJC.2 (fun _ hx => hLJ hx)
    have heq' : L = J := by
      simpa only [map_subgroupOf_eq_of_le hL.1,map_subgroupOf_eq_of_le hJU] using
        congrArg (Subgroup.map (centralizer (U : Set G)).subtype) heq
    exact heq'.symm ▸ hJ
  · exact held_component_lifts_of_odd_center h hm hAU hUV hA hc hJ hn hLJ hL hs he.some (hHeld J he)

/-- The exact E.6.18 consumer for the complete literal catalogue dispatch.
The fields of d and the Held odd-center theorem remain to be supplied. -/
theorem sevenExcluded_of_model_facts
    (d : SevenInspectionModelFacts)
    (hHeld : ∀ (X : Type u) [Group X] [Finite X] [IsQuasisimple X],
      Nonempty ((X ⧸ center X) ≃* Held.He) → Odd (Nat.card (center X)))
    (hA36 : EarlierA36.{u} KnownSimple.IsKnownSimple)
    (hA38 : EarlierA38.{u} KnownSimple.IsKnownSimple)
    {T : Sylow 2 G} (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    [IsElementaryAbelian 2 V] (h15 : HypothesisE615 V) (h8 : SevenEscape M V)
    (h13 : ∀ A ∈ obstructionFamily M V, ¬ (T : Subgroup G) ≤ normalizer (A : Set G)) :
    Enlargement.SevenExcluded M V :=
  sevenExcluded_of_corank_two_lifting h h15 h8 h13
    (corank_two_lifting_of_model_facts d hHeld hA36 hA38 h)
/-- The original known-simple lifting input: the completed earlier A.3.6,
A.3.8, Theorems A/C and orbit/projection sources are all instantiated. -/
theorem corank_two_lifting_knownSimple_of_model_facts
    (d : SevenInspectionModelFacts)
    (hHeld : ∀ (X : Type u) [Group X] [Finite X] [IsQuasisimple X],
      Nonempty ((X ⧸ center X) ≃* Held.He) → Odd (Nat.card (center X)))
    {T : Sylow 2 G} (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    [IsElementaryAbelian 2 V] (hm : 2 < localM V) : SevenCorankTwoLifting V :=
  corank_two_lifting_of_model_facts d hHeld earlierA36_knownSimple earlierA38_knownSimple h hm

/-- Source E.6.18 with every earlier classification, escape and E.6.13
application supplied. Only the concrete model facts, the Held odd center and
the genuine common-normal source input remain. -/
theorem sevenExcluded_knownSimple_of_model_facts
    (d : SevenInspectionModelFacts)
    (hHeld : ∀ (X : Type u) [Group X] [Finite X] [IsQuasisimple X],
      Nonempty ((X ⧸ center X) ≃* Held.He) → Odd (Nat.card (center X)))
    {T : Sylow 2 G} (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    [IsElementaryAbelian 2 V] (h15 : HypothesisE615 V)
    (h311 : InvariantSubspaces.CommonNormalInput KnownSimple.IsKnownSimple T) :
    Enlargement.SevenExcluded M V := by
  apply sevenExcluded_of_corank_two_lifting h h15
    (Components.RemainingSieve.source_sevenEscape h) ?_
    (corank_two_lifting_knownSimple_of_model_facts d hHeld h)
  intro A hA hn
  exact hA.2.2.1 (InvariantSubspaces.centralizer_le_of_normal_in_sylow h h311
    hA.2.1 hA.1 hA.2.2.2
    ((normal_subgroupOf_iff_le_normalizer (hA.1.trans h.le_sylow)).mpr hn))

/-- The literal E.6.18 conclusion with every earlier source theorem supplied.
The remaining premises are the concrete fixed-group facts in `d` and the
Held cover-center theorem; no action inspection or common-normal callback
is assumed. -/
theorem sevenExcluded_of_remaining_model_facts
    (d : SevenInspectionModelFacts)
    (hHeld : ∀ (X : Type u) [Group X] [Finite X] [IsQuasisimple X],
      Nonempty ((X ⧸ center X) ≃* Held.He) → Odd (Nat.card (center X)))
    {T : Sylow 2 G} (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    [IsElementaryAbelian 2 V] (h15 : HypothesisE615 V) :
    Enlargement.SevenExcluded M V :=
  sevenExcluded_knownSimple_of_model_facts d hHeld h h15
    (InvariantSubspaces.source_commonNormalInput_knownSimple T)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
