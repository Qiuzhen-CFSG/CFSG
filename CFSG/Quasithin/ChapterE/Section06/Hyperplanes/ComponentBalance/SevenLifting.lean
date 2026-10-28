module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Rank
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection
public import CFSG.Quasithin.ChapterA.Section02.Statements
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# The exceptional-component inputs to E.6.18

The centralizer of any nonidentity subspace of V lies in that subspace's
two-local normalizer. The genuine E.6.1 hypotheses therefore make it SQTK.
The rank calculation for A₇ and its perfect central three-cover, together
with commuting distinct components, proves uniqueness in these centralizers.

The conditional lifting reduction obtains a normal containing component from
I.3.1(3), applies Theorem A to its central quotient and Theorem C to classify
that quotient, then uses the outstanding model inspection. Component
restriction identifies the containing component with the original one. The
inspection remains unproved; neither uniqueness nor the local rank results
assume it or the later E.6.18 elimination.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.18,
printed p.252; I.3.1(3), pp.414–415; A.3.18, pp.51–52.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V A U L : Subgroup G}

/-- No escaping-centralizer or corank assumption is needed for this SQTK input. -/
theorem subspaceCentralizer_sqtk (h : HypothesisE61 K T M V)
    (hAV : A ≤ V) (hne : A ≠ ⊥) : IsSQTK K (centralizer (A : Set G)) := by
  let _ := h.elementary
  have hn := h.simpleQTKE.twoLocal_sqtk
    (show IsTwoLocal (normalizer (A : Set G)) from
      ⟨A, hne, (IsElementaryAbelian.isPGroup 2 V).to_le hAV, rfl⟩)
  exact (IsSQTK.equiv (subgroupOfEquivOfLe (centralizer_le_normalizer (A : Set G)))).mp
    (hn.subgroup ((centralizer (A : Set G)).subgroupOf (normalizer (A : Set G))))

/-- The exact three-rank needed by I.3.1(3), including the triple-cover case. -/
theorem seven_threeRank_eq_two (h : HypothesisE61 K T M V)
    (hUV : U ≤ V) (hne : U ≠ ⊥) (hL : CentralizerComponent U L)
    (hs : IsSeven L) : primeRank 3 L = 2 := by
  apply le_antisymm _ hs.two_le_primeRank
  have hr := (subspaceCentralizer_sqtk h hUV hne).stronglyQuasithin 3
    (by decide) (by decide)
  exact (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hL.1) (inclusion_injective hL.1)).trans hr

/-- Exceptional components of a nonidentity subspace centralizer coincide.
This discharges the parent's complete uniqueness contract for the full K class. -/
theorem seven_uniqueness (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) :
    SevenUniqueness V := by
  intro A hAV hne L J hL hJ hsL hsJ
  have hr := (subspaceCentralizer_sqtk h hAV hne).stronglyQuasithin 3
    (by decide) (by decide)
  have he := seven_components_eq hr hL.2 hJ.2
    (hsL.of_equiv (subgroupOfEquivOfLe hL.1).symm)
    (hsJ.of_equiv (subgroupOfEquivOfLe hJ.1).symm)
  have hm := congrArg (Subgroup.map (centralizer (A : Set G)).subtype) he
  simpa only [map_subgroupOf_eq_of_le hL.1, map_subgroupOf_eq_of_le hJ.1] using hm

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

omit [Finite G] in
private theorem component_eq_of_containing_centralizing {P L J : Subgroup G} (hL : CentralizerComponent P L)
    (hJ : IsComponent G J) (hLJ : L ≤ J) (hJC : J ≤ centralizer (P : Set G)) : L = J := by
  have he := hL.2.eq_of_le (hJ.subgroupOf hJC) (fun _ hx => hLJ hx)
  have hm := congrArg (Subgroup.map (centralizer (P : Set G)).subtype) he
  simpa only [map_subgroupOf_eq_of_le hL.1, map_subgroupOf_eq_of_le hJC] using hm


private theorem quotient_model
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA CFSG.KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X], IsSimpleGroup X →
      ¬ IsMulCommutative X → IsSQTK CFSG.KnownSimple.IsKnownSimple X →
        Chapter1.Section02.LocalModels.TheoremCModel X)
    {X : Type u} [Group X] [Finite X] [IsQuasisimple X]
    (hX : IsSQTK CFSG.KnownSimple.IsKnownSimple X) :
    Chapter1.Section02.LocalModels.TheoremCModel (X ⧸ center X) := by
  let Q := X ⧸ center X
  let _ : IsSimpleGroup Q := IsQuasisimple.simple
  let _ : IsQuasisimple Q := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center X)) (QuotientGroup.mk'_surjective (center X))
  have htop : IsComponent Q (⊤ : Subgroup Q) :=
    ⟨Subgroup.IsSubnormal.top, IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm⟩
  have hsemi : ChapterA.Section02.IsSemisimple Q := top_unique (le_sSup htop)
  have hsec : ChapterA.Section02.IsSectionOf Q X :=
    .of_surjective (QuotientGroup.mk' (center X)) (QuotientGroup.mk'_surjective (center X))
  apply hC Q inferInstance
  · intro hc
    let _ := hc
    exact Group.IsPerfect.not_isSolvable Q inferInstance
  · exact ⟨(hA X).stronglyQuasithin_section hX.stronglyQuasithin hX.isKGroup hsec hsemi,
      hX.isKGroup.quotient (center X)⟩


/-- Conditional lifting after the genuine I.3.1(3) containing-component input
and the outstanding model inspection. Theorem A supplies SQTK for the actual
central quotient before Theorem C is used; this inheritance is not assumed.
The model inspection must still be proved before the E.6.18 lifting contract
is discharged. The earlier-source inputs are universal, not seven-specific. -/
theorem seven_lifting_of_inspection
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA CFSG.KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X], IsSimpleGroup X →
      ¬ IsMulCommutative X → IsSQTK CFSG.KnownSimple.IsKnownSimple X →
        Chapter1.Section02.LocalModels.TheoremCModel X)
    (hI31 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK CFSG.KnownSimple.IsKnownSimple X → ∀ P D : Subgroup X,
        IsPGroup 2 P → CentralizerComponent P D → primeRank 3 D = 2 →
          ∃ J : Subgroup X, D ≤ J ∧ J.Normal ∧ IsComponent X J)
    (hinspect : ∀ (X : Type u) [Group X] [Finite X] [IsQuasisimple X],
      IsStronglyQuasithin X → Chapter1.Section02.LocalModels.TheoremCModel (X ⧸ center X) →
        SevenActionInspection X)
    (h : HypothesisE61 CFSG.KnownSimple.IsKnownSimple T M V) : SevenLifting V := by
  intro A U L hAU hUV hAne hL hs
  let _ := h.elementary
  let H := centralizer (A : Set G)
  have hH : IsSQTK CFSG.KnownSimple.IsKnownSimple H :=
    subspaceCentralizer_sqtk h (hAU.trans hUV) hAne
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
  have hrD : primeRank 3 D = 2 := by
    apply le_antisymm _ hsD.two_le_primeRank
    exact (Theory.GroupTheory.primeRank_le_of_injective 3 D.subtype D.subtype_injective).trans
      (hH.stronglyQuasithin 3 (by decide) (by decide))
  obtain ⟨J, hDJ, hnJ, hJ⟩ := hI31 H hH P D hP hDP hrD
  let _ := hJ.2
  have hsJ := hH.subgroup J
  let _ := hnJ
  have hJC := (hinspect J hsJ.stronglyQuasithin (quotient_model hA hC hsJ)).modelInspection J
    P D hP hDP hDJ hsD
  have he : D = J := component_eq_of_containing_centralizing hDP hJ hDJ hJC
  refine ⟨hLH, ?_⟩
  change IsComponent H D
  rw [he]
  exact hJ


end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
