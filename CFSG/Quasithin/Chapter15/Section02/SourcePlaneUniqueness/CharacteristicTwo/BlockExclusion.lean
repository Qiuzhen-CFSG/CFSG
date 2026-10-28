module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.LocalReductions
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.Blocks
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.Orbits
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.NaturalCentrality
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Theory.GroupTheory.ConjugateSpanNormalizer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.MaximalImages
public import CFSG.Quasithin.ChapterB.Section03.Offenders.OddParity
public import Theory.Representation.BinaryOffender.FixedCodimTransport

/-!
# The Thompson and action reductions in the preliminary block exclusions

For the original escaping I, use the literal S-orbit X₀ = ⟨X^S⟩,
U₀ = ⟨ZS^X₀⟩ and QI = O₂(KS). Relative normality of a chi-block orbit
is proved inside I. The original uniqueness theorem controls N_G(J(QI));
therefore an escaping orbit with the marked core identity supplies a best
FF*-offender on the actual U₀ action. The odd alternating action then gives
a contradiction. A separate fixed-space argument handles the rank-one route.

These are conditional reductions toward the preliminary part of 15.2.23.
They do not assert that I has no chi-blocks or that every C.1.34 candidate
is a block. The action and parabolic markings remain with this task
(qt-e-152-char2-block-exclusion) after the 18 October consolidation. Earlier Kc orbit clauses
remain with qt-e-152-plane-geometry and qt-e-152-small-parabolic. The enclosing
qt-e-152-plane-characteristic-two task retains their final discharge.

The rank-one argument uses an equality of fixed subgroups, not the printed
unqualified equality ⟨K₀^S⟩ = X₀: the former is the actual module calculation
needed by the proof. No action, quotient or normality convention is changed.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.2.23,
printed pp.1115--1116; B.2.5--10 and B.3.2(4), pp.76--77,83;
refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section04 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The source subgroup QI = O₂(KS); it depends on the original H and plane. -/
abbrev planeParabolicCore (T : Sylow 2 G) (H ZS : Subgroup G) : Subgroup G :=
  ((pResidual 2 H).map H.subtype ⊔ planeSylow T ZS).pCoreIn 2

/-- The source X₀ is the S-conjugate span, not the join XS. -/
abbrev planeBlockOrbit (T : Sylow 2 G) (ZS : Subgroup G)
    {I : Subgroup G} (X : Subgroup I) : Subgroup G :=
  conjugateSpanBy (X.map I.subtype) (planeSylow T ZS)

namespace PlaneUniquenessPreceding
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Relative H-normality of a nontrivial two-subgroup controls its full normalizer. -/
theorem normalizer_le_partner_of_seed_normal
    {R : Subgroup G} (hp : IsPGroup 2 R) (hne : R ≠ ⊥)
    (hn : H ≤ normalizer (R : Set G)) : normalizer (R : Set G) ≤ Mc := by
  obtain ⟨N,hRN,hN⟩ := Finite.exists_le_maximal
    (show IsTwoLocal (normalizer (R : Set G)) from ⟨R,hne,hp,rfl⟩)
  have he : N = Mc := by
    apply Set.mem_singleton_iff.mp
    rw [← d.local_unique]
    exact ⟨hN,hn.trans hRN⟩
  exact hRN.trans_eq he

/-- KS is H-invariant, using the actual index-two S and H = KT. -/
theorem residual_plane_join_normalized (hI : PlaneEscapes Mc ZS I) :
    H ≤ normalizer (((pResidual 2 H).map H.subtype ⊔ planeSylow T ZS : Subgroup G) : Set G) := by
  have hTS : (T : Subgroup G) ≤ normalizer (planeSylow T ZS : Set G) :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mp
      (normal_of_index_eq_two (d.escape_index hI).2)
  have hTK : (T : Subgroup G) ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) :=
    d.geometry.outside.1.1.2.trans
      (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pResidual 2 H)))
  exact d.residual_sup_sylow.ge.trans
    (sup_le (le_sup_left.trans le_normalizer)
      ((le_inf hTK hTS).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)))

/-- Nontriviality of QI comes from the original nontrivial two-core of I. -/
theorem planeParabolicCore_ne_bot (hI : PlaneEscapes Mc ZS I) :
    planeParabolicCore T H ZS ≠ ⊥ := by
  have hQ : I.pCoreIn 2 ≤ (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS :=
    (d.core_le_plane hI).trans le_sup_right
  have hle : I.pCoreIn 2 ≤ planeParabolicCore T H ZS := by
    simpa only [inf_eq_right.mpr hQ] using
      inf_pCoreIn_le_of_le 2 ((d.residual_sup_planeSylow_le hI).trans inf_le_right)
  intro he
  exact hI.1 (bot_unique (hle.trans_eq he))

/-- QI is normal in H, with normality expressed in the original ambient group. -/
theorem planeParabolicCore_normalized (hI : PlaneEscapes Mc ZS I) :
    H ≤ normalizer (planeParabolicCore T H ZS : Set G) :=
  (d.residual_plane_join_normalized hI).trans (normalizer_le_normalizer_intrinsicCore _)

/-- The same QI lies in the original S, with both Sylow embeddings unchanged. -/
theorem planeParabolicCore_le_plane (hI : PlaneEscapes Mc ZS I) :
    planeParabolicCore T H ZS ≤ planeSylow T ZS := by
  have hTH : (T : Subgroup G) ≤ H := d.geometry.outside.1.1.2
  have hQH : planeParabolicCore T H ZS ≤ H.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes
      (sup_le (map_subtype_le _) (inf_le_left.trans hTH))
      (d.residual_plane_join_normalized hI)
  have hHT := pCoreIn_le_sylow H (T.subtype hTH)
  rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] at hHT
  exact le_inf (hQH.trans hHT)
    ((pCoreIn_le 2 _).trans (sup_le d.residual_centralizes inf_le_right))

/-- The source uniqueness theorem controls the full Thompson normalizer. -/
theorem planeParabolicCore_thompson_normalizer_le (hI : PlaneEscapes Mc ZS I) :
    normalizer (elementaryAbelianMaxJ (planeParabolicCore T H ZS) : Set G) ≤ Mc := by
  let Q := planeParabolicCore T H ZS
  have hJQ : elementaryAbelianMaxJ Q ≤ Q := sSup_le fun _ hA => hA.1
  exact d.normalizer_le_partner_of_seed_normal
    ((isPGroup_pCoreIn 2 _).to_le hJQ)
    (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup Q (isPGroup_pCoreIn 2 _)
      (d.planeParabolicCore_ne_bot hI))
    ((d.planeParabolicCore_normalized hI).trans
      (normalizer_le_normalizer_elementaryAbelianMaxJ Q))

/-- The Thompson subgroup cannot lie in the two-core of an escaping extension.
The core bound is the precise output of the M₀QI calculation in each model. -/
theorem planeParabolicCore_thompson_not_le_core
    (hI : PlaneEscapes Mc ZS I) {X0 : Subgroup G} (hout : ¬ X0 ≤ Mc)
    (hcore : (X0 ⊔ planeParabolicCore T H ZS).pCoreIn 2 ≤ planeParabolicCore T H ZS) :
    ¬ elementaryAbelianMaxJ (planeParabolicCore T H ZS) ≤
      (X0 ⊔ planeParabolicCore T H ZS).pCoreIn 2 := by
  intro hj
  have he := elementaryAbelianMaxJ_eq_of_intermediate_finite
    (planeParabolicCore T H ZS) _ hj hcore
  have hn : X0 ≤ normalizer
      (elementaryAbelianMaxJ (planeParabolicCore T H ZS) : Set G) := by
    rw [← he]
    exact le_sup_left.trans ((X0 ⊔ planeParabolicCore T H ZS).le_normalizer.trans
      ((normalizer_le_normalizer_intrinsicCore _).trans
        (normalizer_le_normalizer_elementaryAbelianMaxJ _)))
  exact hout (hn.trans (d.planeParabolicCore_thompson_normalizer_le hI))

/-- A chi-block has a normal S-orbit inside the original I. -/
theorem chi_orbit_normalized (hI : PlaneEscapes Mc ZS I)
    (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsChiBlockIn X) :
    I ≤ normalizer (planeBlockOrbit T ZS X : Set G) := by
  obtain ⟨P,hP⟩ := d.sylow_in_escape hI
  have hs := (Chapter3.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin
  let Y := conjugateSpanBy X (P : Subgroup I)
  let : Y.Normal := conjugateSpanBy_sylow_normal X P
    (ChapterC.RankOne.ChiProduct.normal_or_index_two hfit (hs 3 (by decide) (by decide)) hX)
  have he : Y.map I.subtype = planeBlockOrbit T ZS X := by
    rw [map_conjugateSpanBy,hP]
  rw [← he]
  intro x hx
  apply le_normalizer_map I.subtype
  exact ⟨⟨x,hx⟩, by rw [normalizer_eq_top]; trivial, rfl⟩

/-- The literal orbit of every subgroup of I still lies in I. -/
theorem blockOrbit_le_escape (hI : PlaneEscapes Mc ZS I) (X : Subgroup I) :
    planeBlockOrbit T ZS X ≤ I :=
  conjugateSpanBy_le (map_subtype_le X)
    (((le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right).trans I.le_normalizer)

/-- In characteristic two the original plane lies in Ω₁Z(O₂(I)). -/
theorem plane_le_escape_core_omega
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I) :
    ZS ≤ omegaOneCenterAmbient (I.pCoreIn 2) := by
  have hSI : planeSylow T ZS ≤ I :=
    (le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  intro z hz
  have hzS := (mem_omegaOneCenterAmbient_iff _ z).mp (d.omega_center ▸ hz)
  have hc : ∀ q ∈ I.pCoreIn 2, q * z = z * q :=
    fun q hq => hzS.2.2 q (d.core_le_plane hI hq)
  have hzQ : z ∈ I.pCoreIn 2 := by
    have hzC : (⟨z,hSI hzS.1⟩ : I) ∈ centralizer (pCore 2 I : Set I) := by
      intro q hq
      apply Subtype.ext
      exact hc q (mem_map_of_mem I.subtype hq)
    have hself : centralizer (pCore 2 I : Set I) ≤ pCore 2 I := by
      rw [← hfit]
      exact centralizer_generalizedFitting_le I
    exact mem_map_of_mem I.subtype (hself hzC)
  exact (mem_omegaOneCenterAmbient_iff _ z).mpr ⟨hzQ,hzS.2.1,hc⟩

/-- The literal U₀ is elementary: all its conjugates lie in Ω₁Z(O₂(I)). -/
theorem plane_span_elementary
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X0 : Subgroup G} (hXI : X0 ≤ I) :
    IsElementaryAbelian 2 (conjugateSpanBy ZS X0) := by
  have hU : conjugateSpanBy ZS X0 ≤ omegaOneCenterAmbient (I.pCoreIn 2) :=
    conjugateSpanBy_le (d.plane_le_escape_core_omega hI hfit)
      (hXI.trans (I.le_normalizer.trans ((normalizer_le_normalizer_intrinsicCore I).trans
        (normalizer_le_normalizer_omegaCenter _))))
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (I.pCoreIn 2)) :=
    omegaOneCenterAmbient_elementaryAbelian _
  exact IsElementaryAbelian.of_injective (inclusion hU) (inclusion_injective hU)

/-- The source plane is already in QI in the characteristic-two branch. -/
theorem plane_le_planeParabolicCore
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I) :
    ZS ≤ planeParabolicCore T H ZS := by
  have hQ : I.pCoreIn 2 ≤ (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS :=
    (d.core_le_plane hI).trans le_sup_right
  have hle : I.pCoreIn 2 ≤ planeParabolicCore T H ZS := by
    simpa only [inf_eq_right.mpr hQ] using
      inf_pCoreIn_le_of_le 2 ((d.residual_sup_planeSylow_le hI).trans inf_le_right)
  have hOmega : omegaOneCenterAmbient (I.pCoreIn 2) ≤ I.pCoreIn 2 :=
    fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  exact (d.plane_le_escape_core_omega hI hfit).trans (hOmega.trans hle)

/-- The complete orbit span U₀, not just its seed plane, lies in QI. -/
theorem plane_span_le_planeParabolicCore
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X0 : Subgroup G} (hXI : X0 ≤ I) :
    conjugateSpanBy ZS X0 ≤ planeParabolicCore T H ZS := by
  have hOmega : omegaOneCenterAmbient (I.pCoreIn 2) ≤ I.pCoreIn 2 :=
    fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hU : conjugateSpanBy ZS X0 ≤ I.pCoreIn 2 :=
    conjugateSpanBy_le ((d.plane_le_escape_core_omega hI hfit).trans hOmega)
      (hXI.trans (I.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore I)))
  have hQ : I.pCoreIn 2 ≤ (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS :=
    (d.core_le_plane hI).trans le_sup_right
  apply hU.trans
  simpa only [inf_eq_right.mpr hQ] using
    inf_pCoreIn_le_of_le 2 ((d.residual_sup_planeSylow_le hI).trans inf_le_right)

/-- The whole span U₀ is normalized by X₀QI, using relative normality of X₀. -/
theorem plane_span_normalized (hI : PlaneEscapes Mc ZS I)
    {X0 : Subgroup G} (hn : I ≤ normalizer (X0 : Set G)) :
    X0 ⊔ planeParabolicCore T H ZS ≤ normalizer (conjugateSpanBy ZS X0 : Set G) := by
  have hQI : planeParabolicCore T H ZS ≤ I :=
    (pCoreIn_le 2 _).trans ((d.residual_sup_planeSylow_le hI).trans inf_le_right)
  have hQZ : planeParabolicCore T H ZS ≤ centralizer (ZS : Set G) :=
    (pCoreIn_le 2 _).trans (sup_le d.residual_centralizes inf_le_right)
  exact sup_le (le_normalizer_conjugateSpanBy ZS X0)
    (normalizes_conjugateSpanBy ZS X0 _
      (hQZ.trans (Subgroup.centralizer_le_normalizer _)) (hQI.trans hn))

/-- The normal-perfect reduction applies to the actual S-orbit, whose relative
normality has been discharged from the chi-block hypothesis. -/
theorem perfect_chi_orbit_not_le_partner
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsChiBlockIn X)
    [Group.IsPerfect (planeBlockOrbit T ZS X)]
    (hres : primeToResidual 3 (planeBlockOrbit T ZS X) = ⊤)
    (hmove : intrinsicSignalizerModule (planeBlockOrbit T ZS X) ≠ ⊥) :
    ¬ planeBlockOrbit T ZS X ≤ Mc := by
  intro hMc
  exact d.no_normal_perfect_threeResidual horbit hI
    (d.blockOrbit_le_escape hI X) (d.chi_orbit_normalized hI hfit hX) hMc hres hmove

/-- The literal QI-action on U₀ contains an FF*-offender. Here FF* means
`IsBestOffender`, not the strictly stronger `IsStrongOffender`.
The only model input is the actual centralizer/core identity. -/
theorem plane_span_bestOffender
    (hI : PlaneEscapes Mc ZS I) {X0 : Subgroup G} (hout : ¬ X0 ≤ Mc)
    (U : Subgroup (X0 ⊔ planeParabolicCore T H ZS : Subgroup G))
    [U.Normal] [IsElementaryAbelian 2 U]
    (hU : U.map (X0 ⊔ planeParabolicCore T H ZS).subtype = conjugateSpanBy ZS X0)
    (hcore : (X0 ⊔ planeParabolicCore T H ZS).pCoreIn 2 =
      planeParabolicCore T H ZS ⊓ centralizer (conjugateSpanBy ZS X0 : Set G))
    {D : Type*} [Group D] [Finite D]
    (q : (X0 ⊔ planeParabolicCore T H ZS : Subgroup G) →* D)
    (hq : Function.Surjective q) (hker : q.ker = centralizer (U : Set _)) :
    ∃ A ∈ elementaryAbelianMaxSubgroups
        ((planeParabolicCore T H ZS).subgroupOf (X0 ⊔ planeParabolicCore T H ZS)),
      Representation.BinaryOffender.IsBestOffender
        (Representation.NormalElementaryQuotient.representation U q hq hker) (A.map q) := by
  classical
  let Q := planeParabolicCore T H ZS
  let E := X0 ⊔ Q
  let R := Q.subgroupOf E
  have hR : R.map E.subtype = Q := map_subgroupOf_eq_of_le le_sup_right
  have hJ : (elementaryAbelianMaxJ R).map E.subtype = elementaryAbelianMaxJ Q := by
    rw [← elementaryAbelianMaxJ_map_injective E.subtype E.subtype_injective,hR]
  have hUR : U ≤ R := by
    have hu : U ≤ pCore 2 E := le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩
    intro u hu'
    exact (hcore ▸ (show (u : G) ∈ E.pCoreIn 2 from
      mem_map_of_mem E.subtype (hu hu'))).1
  have hj : ¬ elementaryAbelianMaxJ R ≤ q.ker := by
    intro hj
    apply d.planeParabolicCore_thompson_not_le_core hI hout (hcore.le.trans inf_le_left)
    rw [hcore]
    refine le_inf (sSup_le fun _ hA => hA.1) ?_
    rw [← hJ,← hU]
    rintro _ ⟨a,ha,rfl⟩ b ⟨b,hb,rfl⟩
    exact congrArg E.subtype ((hker ▸ hj ha) b hb)
  obtain ⟨A,hA,hne⟩ : ∃ A ∈ elementaryAbelianMaxSubgroups R, A.map q ≠ ⊥ := by
    by_contra! hh
    exact hj (sSup_le fun A hA => (Subgroup.map_eq_bot_iff A).mp (hh A hA))
  exact ⟨A,hA,Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
    U q hq hker R A hUR hA hne⟩

open scoped Pointwise in
/-- The Borel/partition/parabolic marking yields the actual centralizer-core
identity. Its normality premise is relative to KS, not ambient G. This is
the group-theoretic part of the core calculation on printed p.1115. -/
theorem plane_span_centralizer_core
    (hI : PlaneEscapes Mc ZS I) {X0 : Subgroup G}
    (hn : I ≤ normalizer (X0 : Set G))
    (hmark : X0 ⊓ centralizer (ZS : Set G) ≤
      (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS)
    (hmark_normal : (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS ≤
      normalizer ((X0 ⊓ centralizer (ZS : Set G) : Subgroup G) : Set G)) :
    ((X0 ⊔ planeParabolicCore T H ZS) ⊓ centralizer (ZS : Set G)).pCoreIn 2 =
      planeParabolicCore T H ZS := by
  let P := (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS
  let Q := planeParabolicCore T H ZS
  let B := X0 ⊓ centralizer (ZS : Set G)
  let C := (X0 ⊔ Q) ⊓ centralizer (ZS : Set G)
  have hQP : Q ≤ P := pCoreIn_le 2 P
  have hQZ : Q ≤ centralizer (ZS : Set G) :=
    hQP.trans (sup_le d.residual_centralizes inf_le_right)
  have hQI : Q ≤ I := hQP.trans ((d.residual_sup_planeSylow_le hI).trans inf_le_right)
  have hCQ : C = B ⊔ Q := by
    apply le_antisymm
    · intro g hg
      have hgprod : g ∈ (X0 : Set G) * (Q : Set G) := by
        rw [← coe_mul_of_right_le_normalizer_left X0 Q (hQI.trans hn)]
        exact hg.1
      obtain ⟨x,hx,q,hq,he⟩ := hgprod
      have hxZ : x ∈ centralizer (ZS : Set G) := by
        have hh := (centralizer (ZS : Set G)).mul_mem hg.2
          ((centralizer (ZS : Set G)).inv_mem (hQZ hq))
        rw [← he,mul_inv_cancel_right] at hh
        exact hh
      exact he ▸ mul_mem_sup (show x ∈ B from ⟨hx,hxZ⟩) hq
    · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
        (le_inf le_sup_right hQZ)
  have hCP : C ≤ P := hCQ ▸ sup_le hmark hQP
  have hPQ : P ≤ normalizer (Q : Set G) :=
    P.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore P)
  have hPC : P ≤ normalizer (C : Set G) := by
    rw [hCQ]
    exact (le_inf hmark_normal hPQ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  apply le_antisymm (pCoreIn_mono_of_normalizes hCP hPC)
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 P)
    (le_inf le_sup_right hQZ) (hCP.trans hPQ)

/-- Apply the offender reduction to the literal subgroup U₀ inside X₀QI.
Both its relative normality and its elementary abelian structure are discharged.
Only the marked core/centralizer identity remains a model input. -/
theorem plane_span_canonical_bestOffender
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X0 : Subgroup G} (hXI : X0 ≤ I) (hn : I ≤ normalizer (X0 : Set G))
    (hout : ¬ X0 ≤ Mc)
    (hcore : (X0 ⊔ planeParabolicCore T H ZS).pCoreIn 2 =
      planeParabolicCore T H ZS ⊓ centralizer (conjugateSpanBy ZS X0 : Set G)) :
    let E := X0 ⊔ planeParabolicCore T H ZS
    let U := (conjugateSpanBy ZS X0).subgroupOf E
    ∃ hnormal : U.Normal, ∃ helementary : IsElementaryAbelian 2 U,
      letI := hnormal
      letI := helementary
      let C := centralizer (U : Set E)
      let q := QuotientGroup.mk' C
      ∃ A ∈ elementaryAbelianMaxSubgroups ((planeParabolicCore T H ZS).subgroupOf E),
        Representation.BinaryOffender.IsBestOffender
          (Representation.NormalElementaryQuotient.representation U q
            (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)) (A.map q) := by
  let E := X0 ⊔ planeParabolicCore T H ZS
  let U := (conjugateSpanBy ZS X0).subgroupOf E
  have hUE : conjugateSpanBy ZS X0 ≤ E :=
    (d.plane_span_le_planeParabolicCore hI hfit hXI).trans le_sup_right
  let hnU : U.Normal := normal_subgroupOf_of_le_normalizer (d.plane_span_normalized hI hn)
  let : IsElementaryAbelian 2 (conjugateSpanBy ZS X0) := d.plane_span_elementary hI hfit hXI
  let heU : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUE
  refine ⟨hnU,heU,?_⟩
  exact d.plane_span_bestOffender hI hout U (map_subgroupOf_eq_of_le hUE) hcore
    (QuotientGroup.mk' (centralizer (U : Set E)))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

/-- B.3.2(4) on the actual QI-image: a five- or seven-point core model with
even QI-image is incompatible with the offender just constructed. The
injective actor map and fixed codimensions specify the literal action;
no assertion that a family label has no offenders is assumed. -/
theorem alternating_plane_span_false
    (hI : PlaneEscapes Mc ZS I) {X0 : Subgroup G} (hout : ¬ X0 ≤ Mc)
    (U : Subgroup (X0 ⊔ planeParabolicCore T H ZS : Subgroup G))
    [U.Normal] [IsElementaryAbelian 2 U]
    (hU : U.map (X0 ⊔ planeParabolicCore T H ZS).subtype = conjugateSpanBy ZS X0)
    (hcore : (X0 ⊔ planeParabolicCore T H ZS).pCoreIn 2 =
      planeParabolicCore T H ZS ⊓ centralizer (conjugateSpanBy ZS X0 : Set G))
    {D : Type*} [Group D] [Finite D]
    (q : (X0 ⊔ planeParabolicCore T H ZS : Subgroup G) →* D)
    (hq : Function.Surjective q) (hker : q.ker = centralizer (U : Set _))
    {n : ℕ} (hn : n = 5 ∨ n = 7)
    (f : D →* Equiv.Perm (Fin n)) (hf : Function.Injective f)
    (hcodim : ∀ A : Subgroup D,
      Representation.BinaryOffender.fixedCodim
        (Representation.NormalElementaryQuotient.representation U q hq hker) A =
      Representation.BinaryOffender.fixedCodim
        (BinaryPermutation.coreRepresentation (Fin n)) (A.map f))
    (heven : (((planeParabolicCore T H ZS).subgroupOf
      (X0 ⊔ planeParabolicCore T H ZS)).map q).map f ≤ alternatingGroup (Fin n)) :
    False := by
  obtain ⟨A,hA,hoff⟩ := d.plane_span_bestOffender hI hout U hU hcore q hq hker
  have hmodel := hoff.map_of_fixedCodim
    (Representation.NormalElementaryQuotient.representation U q hq hker)
    (BinaryPermutation.coreRepresentation (Fin n)) f hf hcodim
  exact ChapterB.Offenders.core_offender_not_le_alternating hn
    (hmodel.isOffender _) ((map_mono (map_mono hA.1)).trans heven)

/-- The A₃/L₂ fixed-space reduction on the actual plane span. The model
producer supplies equality of fixed subgroups for the S-orbit of the cubic
intersection; no equality of that solvable orbit with X₀ is assumed. -/
theorem rankOne_cubic_fixed_space_false {X : Subgroup I}
    (hfixed :
      let K := (pResidual 2 H).map H.subtype
      let K0 := (pResidual 2 (K ⊓ X.map I.subtype : Subgroup G)).map
        (K ⊓ X.map I.subtype).subtype
      let X0 := planeBlockOrbit T ZS X
      let U0 := conjugateSpanBy ZS X0
      U0 ⊓ centralizer (conjugateSpanBy K0 (planeSylow T ZS) : Set G) =
        U0 ⊓ centralizer (X0 : Set G))
    (hmove : ¬ ZS ⊓ conjugateSpanBy ZS (planeBlockOrbit T ZS X) ≤
      centralizer (planeBlockOrbit T ZS X : Set G)) : False := by
  let K := (pResidual 2 H).map H.subtype
  let K0 := (pResidual 2 (K ⊓ X.map I.subtype : Subgroup G)).map
    (K ⊓ X.map I.subtype).subtype
  let Y0 := conjugateSpanBy K0 (planeSylow T ZS)
  let X0 := planeBlockOrbit T ZS X
  let U0 := conjugateSpanBy ZS X0
  have hYK : Y0 ≤ K := conjugateSpanBy_le ((map_subtype_le _).trans inf_le_left)
    ((inf_le_left.trans d.geometry.outside.1.1.2).trans
      (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))))
  have hZY : ZS ≤ centralizer (Y0 : Set G) :=
    le_centralizer_iff.mp (hYK.trans d.residual_centralizes)
  apply hmove
  intro z hz
  have hf : z ∈ U0 ⊓ centralizer (Y0 : Set G) := ⟨hz.2,hZY hz.1⟩
  change U0 ⊓ centralizer (Y0 : Set G) = U0 ⊓ centralizer (X0 : Set G) at hfixed
  exact (hfixed ▸ hf).2

/-! The natural-block rank-one route can be discharged from an actual odd
subgroup in the block.  This is the literal source input needed in the
`L₂(2ⁿ)` row; it does not identify the solvable orbit span with `X₀`. -/

theorem l2_block_le_partner_of_odd_fixed
    (hI : PlaneEscapes Mc ZS I)
    (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X)
    {n : ℕ} (hn : ChapterC.IsL2EvenBlock X n)
    (D : Subgroup I) (hDX : D ≤ X)
    (hodd : Odd (Nat.card D)) (hD : D ≠ ⊥)
    (hDK : D ≤ ((pResidual 2 H).map H.subtype).subgroupOf I) :
    X.map I.subtype ≤ Mc := by
  obtain ⟨R,hR⟩ := d.sylow_in_escape hI
  have hZI : ZS ≤ I := d.plane_le_centralizer.trans
    ((d.centralizer_le_intersection hI).trans inf_le_right)
  have hZX : ZS ≤ centralizer (X.map I.subtype : Set G) := by
    intro z hz
    have hzS := (mem_omegaOneCenterAmbient_iff _ _).mp (d.omega_center ▸ hz)
    have hzR : (⟨z,hZI hz⟩ : I) ∈ centralizer (R : Set I) := by
      intro r hr
      exact Subtype.ext (hzS.2.2 r (hR ▸ mem_map_of_mem I.subtype hr))
    have hzD : (⟨z,hZI hz⟩ : I) ∈ centralizer (D : Set I) := by
      intro a ha
      exact Subtype.ext ((d.residual_centralizes (hDK ha)) z hz).symm
    have hzX := hn.centralizes_of_sylow_and_odd_fixed R hfit X hX D hDX hodd hD
      ⟨z,hZI hz⟩ (Subtype.ext hzS.2.1) hzR hzD
    rintro x ⟨x,hx,rfl⟩
    exact congrArg I.subtype (hzX x hx)
  exact (le_centralizer_iff.mp hZX).trans ((d.centralizer_le_intersection hI).trans inf_le_left)

/-- The original chi-block application combines relative orbit normality,
the Kc preliminary exclusion and the actual odd alternating action. The
remaining premises are the orbit and action markings supplied by the block
model producer; they are not a no-chi-block hypothesis. -/
theorem alternating_chi_false_of_marked_action
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsChiBlockIn X)
    [Group.IsPerfect (planeBlockOrbit T ZS X)]
    (hres : primeToResidual 3 (planeBlockOrbit T ZS X) = ⊤)
    (hmove : intrinsicSignalizerModule (planeBlockOrbit T ZS X) ≠ ⊥)
    (U : Subgroup (planeBlockOrbit T ZS X ⊔ planeParabolicCore T H ZS : Subgroup G))
    [U.Normal] [IsElementaryAbelian 2 U]
    (hU : U.map (planeBlockOrbit T ZS X ⊔ planeParabolicCore T H ZS).subtype =
      conjugateSpanBy ZS (planeBlockOrbit T ZS X))
    (hcore : (planeBlockOrbit T ZS X ⊔ planeParabolicCore T H ZS).pCoreIn 2 =
      planeParabolicCore T H ZS ⊓ centralizer
        (conjugateSpanBy ZS (planeBlockOrbit T ZS X) : Set G))
    {D : Type*} [Group D] [Finite D]
    (q : (planeBlockOrbit T ZS X ⊔ planeParabolicCore T H ZS : Subgroup G) →* D)
    (hq : Function.Surjective q) (hker : q.ker = centralizer (U : Set _))
    {n : ℕ} (hn : n = 5 ∨ n = 7)
    (f : D →* Equiv.Perm (Fin n)) (hf : Function.Injective f)
    (hcodim : ∀ A : Subgroup D,
      Representation.BinaryOffender.fixedCodim
        (Representation.NormalElementaryQuotient.representation U q hq hker) A =
      Representation.BinaryOffender.fixedCodim
        (BinaryPermutation.coreRepresentation (Fin n)) (A.map f))
    (heven : (((planeParabolicCore T H ZS).subgroupOf
      (planeBlockOrbit T ZS X ⊔ planeParabolicCore T H ZS)).map q).map f ≤
        alternatingGroup (Fin n)) : False :=
  d.alternating_plane_span_false hI
    (d.perfect_chi_orbit_not_le_partner horbit hI hfit hX hres hmove)
    U hU hcore q hq hker hn f hf hcodim heven

/-- The C.1.28 endpoint on the original NI and MI. This is only the final
assembly step: the no-chi-block premise remains to be proved from the model
reductions above before the first branch of 15.2.23 is complete. -/
theorem characteristicTwo_false_of_intersection_le
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hNI : M ⊓ I ≤ Mc ⊓ I)
    (hblocks : ∀ X : Subgroup I, ¬ ChapterC.IsChiBlockIn X) : False := by
  obtain ⟨X,hX,_⟩ := d.escaping_chi_block_of_intersection_le hI hfit hNI
  exact hblocks X hX

end PlaneUniquenessPreceding
end CFSG.Quasithin.Chapter15.Section02
