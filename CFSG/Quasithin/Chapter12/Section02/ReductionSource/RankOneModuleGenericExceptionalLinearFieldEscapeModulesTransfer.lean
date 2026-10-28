module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesOrbitCubic
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesChiefFour
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesStarred

/-!
# Small cubic offenders on the original centralizer span

The strict cubic bound on the existing residual orbit quotient excludes
faithful small cubic actors. D.2.7 and the restriction transfer strengthen
this to centralization of the original residual image by every minimum
cubic offender. The generalized-Fitting decomposition then selects an
actual component of its centralizer moved by that same offender; its order
is prime to three. All subgroups use the original projection and Sylow.

The last application discharges the small-ratio premise using the original
chief count, retaining middle-layer fixedness as an explicit hypothesis.
That geometric premise and the Suzuki component exclusion remain open;
this module does not assert the abelian-span conclusion of 5.1.23.
Source: Aschbacher--Smith D.2.7 and 5.1.23, printed pp.180,645--646,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

/-- Every small cubic in the original Sylow image has a nonidentity
element centralizing the original residual image. -/
theorem linear_cubic_small_actor_centralizer_ne_bot
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (d : CubicEscape.LocalData T H C z)
    (E : Subgroup (SpanAction.Actor (linear_cubic_centralizer_setup h d)))
    (hEP : E ≤ ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))).map
      (SpanAction.projection (linear_cubic_centralizer_setup h d)))
    (hE : IsElementaryTwo E)
    (hc : IsCubic (SpanAction.representation (linear_cubic_centralizer_setup h d)) E)
    (hr : actionRatio (SpanAction.representation (linear_cubic_centralizer_setup h d)) E ≤ 2) :
    let s := linear_cubic_centralizer_setup h d
    let K := ((residual H).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
    E ⊓ centralizer (K : Set (SpanAction.Actor s)) ≠ ⊥ := by
  obtain ⟨hN,hm⟩ := linear_cubic_residual_image h hH hK hnf hlinear d
  let := (ChapterK.Linear.Recognition.PSL3FourExclusion.model_facts hm).1
  exact SpanAction.small_cubic_residual_centralizer_ne_bot _ _ _
    (linear_cubic_residual_orbit_section h hH hK hnf hlinear d)
    (linear_cubic_residual_orbit_cubicRatio_gt_two D h hH hK hnf hlinear d)
    hEP hE hc hr

/-- D.2.7 and the strict bound on the same orbit force every minimum
cubic offender in the original Sylow image to centralize the residual image. -/
theorem linear_cubic_starred_centralizes_residual
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (d : CubicEscape.LocalData T H C z)
    (E : Subgroup (SpanAction.Actor (linear_cubic_centralizer_setup h d)))
    (hEP : E ≤ ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))).map
      (SpanAction.projection (linear_cubic_centralizer_setup h d)))
    (hE : E ∈ ChapterD.QhatStar
      (SpanAction.representation (linear_cubic_centralizer_setup h d))) :
    let s := linear_cubic_centralizer_setup h d
    let K := ((residual H).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
    E ≤ centralizer (K : Set (SpanAction.Actor s)) := by
  obtain ⟨hN,hm⟩ := linear_cubic_residual_image h hH hK hnf hlinear d
  let := (ChapterK.Linear.Recognition.PSL3FourExclusion.model_facts hm).1
  exact SpanAction.starred_centralizes_residual_of_orbit_bound _ _ _
    (T.isPGroup'.comap_subtype.map (SpanAction.projection (linear_cubic_centralizer_setup h d)))
    (linear_cubic_residual_orbit_section h hH hK hnf hlinear d)
    (linear_cubic_residual_orbit_cubicRatio_gt_two D h hH hK hnf hlinear d)
    hEP hE

/-- The faithful residual branch is excluded; the same minimum offender
moves an actual component of the three-prime residual centralizer. -/
theorem linear_cubic_minimum_moves_centralizer_component
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (d : CubicEscape.LocalData T H C z)
    (hsmall : cubicRatio (SpanAction.representation (linear_cubic_centralizer_setup h d)) < 2) :
    let s := linear_cubic_centralizer_setup h d
    let K := ((residual H).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
    let Z := centralizer (K : Set (SpanAction.Actor s))
    ∃ E : Subgroup (SpanAction.Actor s),
      E ≤ ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))).map
        (SpanAction.projection s) ∧ E ∈ ChapterD.QhatStar (SpanAction.representation s) ∧
      E ≤ Z ∧ E ⊓ Z ≠ ⊥ ∧ ∃ J : Subgroup Z,
        IsComponent Z J ∧ IsComponent (SpanAction.Actor s) (J.map Z.subtype) ∧
        Nat.Coprime 3 (Nat.card J) ∧
        ⁅J.map Z.subtype,E ⊓ Z⁆ ≠ ⊥ ∧ ⁅J.map Z.subtype,E⁆ ≠ ⊥ := by
  let s := linear_cubic_centralizer_setup h d
  let K := ((residual H).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
  let P := ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
  let Z := centralizer (K : Set (SpanAction.Actor s))
  obtain ⟨hN,hm⟩ := linear_cubic_residual_image h hH hK hnf hlinear d
  let := hN
  let := (ChapterK.Linear.Recognition.PSL3FourExclusion.model_facts hm).1
  obtain ⟨E,hEP,hE,hF⟩ := linear_cubic_minimum_fitting_centralization h hH hK hnf hlinear d hsmall
  rw [linear_cubic_centralizer_image h hH hK hnf d] at hF
  have hr : actionRatio (SpanAction.representation s) E ≤ 2 :=
    hE.1.2.2.2.trans_le hsmall.le
  obtain ⟨hne,J,hJ,hJX,hmove,hmove'⟩ :=
    SpanAction.small_cubic_moves_centralizer_component (SpanAction.representation s) K P
      (SpanAction.actor_core_eq_bot s)
      (linear_cubic_residual_orbit_section h hH hK hnf hlinear d)
      (linear_cubic_residual_orbit_cubicRatio_gt_two D h hH hK hnf hlinear d)
      hEP hE.1.2.1 hE.1.2.2.1 hr hF
  have hEZ := linear_cubic_starred_centralizes_residual D h hH hK hnf hlinear d E hEP hE
  exact ⟨E,hEP,hE,hEZ,hne,J,hJ,hJX,
    (linear_cubic_residual_centralizer_three_prime h hH hK hnf hlinear d).coprime_dvd_right
      J.card_subgroup_dvd_card,hmove,hmove'⟩

/-- The original chief-count and fixed-layer inputs feed the component
selection; no faithful-residual alternative or extra ratio premise remains. -/
theorem linear_cubic_centralizer_component_of_middle_fixed
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G)))) (hn : 1 < n)
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G))
    (hfix : let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
      ⁅conjugate (S.W g) g,S.S₂ g⁆ ≤ zpowers z) :
    let s := linear_cubic_centralizer_setup h d
    let K := ((residual H).subgroupOf (centralizer ({z} : Set G))).map (SpanAction.projection s)
    let Z := centralizer (K : Set (SpanAction.Actor s))
    ∃ E : Subgroup (SpanAction.Actor s),
      E ≤ ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))).map
        (SpanAction.projection s) ∧ E ∈ ChapterD.QhatStar (SpanAction.representation s) ∧
      E ≤ Z ∧ E ⊓ Z ≠ ⊥ ∧ ∃ J : Subgroup Z,
        IsComponent Z J ∧ IsComponent (SpanAction.Actor s) (J.map Z.subtype) ∧
        Nat.Coprime 3 (Nat.card J) ∧
        ⁅J.map Z.subtype,E ⊓ Z⁆ ≠ ⊥ ∧ ⁅J.map Z.subtype,E⁆ ≠ ⊥ := by
  exact linear_cubic_minimum_moves_centralizer_component D h hH hK hnf hlinear d
    (linear_cubic_strict_cubic_of_middle_fixed D h hpsl c d hne hn g hg hgn hfix)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
