module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.LinearThree.Centralizer
public import Theory.GroupTheory.PCorePrimeToIndex
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Escape of an actual binary MS component and its Sylow orbit

MS2 puts O₂(XR) inside R. If the intrinsic signalizer module of X
vanished, A.4.8 would make X centralize Ω₁Z(O₂(XR)), hence Ω₁Z(R).
The latter is a nontrivial characteristic subgroup of R, central in XR,
contradicting MS3. This argument uses the actual MS hypotheses and no
classification alternative or nonzero-module premise.

The module stays nonzero in the subnormal S-orbit. That orbit is perfect,
normal in I and its own prime-to-three residual. The already proved first
preliminary exclusion of 15.2.23 puts the orbit and X outside Mc. Applying
the original-component centralizer theorem now supplies its maximal
parabolic and KS containment with no escape callback.

The remaining exchanged-orbit marking and the centralizer of the local
Sylow omega-center belong to qt-e-152-char2-block-exclusion. The explicit
earlier Kc orbit alternative is produced by the small-parabolic and
plane-geometry owners and discharged in the enclosing characteristic-two
assembly. This module does not identify the MS radical R with QI.

Source: Aschbacher--Smith, preliminary 15.2.23, printed p.1115;
A.4.8, printed p.59; C.1.31--34, printed pp.135--137, refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterA.Section04
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- MS2 puts the extension core in its actual radical R. -/
theorem linearThreeMS_twoCore_le {X R : Subgroup G} {n : ℕ} {F : Type}
    [Field F] [Finite F] (hms : LinearThreeMSPair KnownSimple.IsKnownSimple X R n F) :
    (X ⊔ R).pCoreIn 2 ≤ R := by
  rcases hms.radical with ⟨A,hA,ho,hcore⟩ | h
  · have hh := pCore_le_map_pCore_of_prime_not_dvd_index
      (A.subgroupOf (X ⊔ R)) ho.not_two_dvd_nat
    have hm := map_mono hh (f := (X ⊔ R).subtype)
    change (X ⊔ R).pCoreIn 2 ≤ ((A.subgroupOf (X ⊔ R)).pCoreIn 2).map
      (X ⊔ R).subtype at hm
    rwa [map_pCoreIn_of_injective 2 _ _ (X ⊔ R).subtype_injective,
      map_subgroupOf_eq_of_le hA.le,hcore] at hm
  · exact h.1

/-- The genuine MS characteristic condition forces a nonzero intrinsic
signalizer module; no module classification is required. -/
theorem linearThreeMS_intrinsicModule_ne_bot {X R : Subgroup G} {n : ℕ} {F : Type}
    [Field F] [Finite F] (hms : LinearThreeMSPair KnownSimple.IsKnownSimple X R n F)
    (hpR : IsPGroup 2 R) : intrinsicSignalizerModule X ≠ ⊥ := by
  let J := X ⊔ R
  let N := J.pCoreIn 2
  have hNR : N ≤ R := linearThreeMS_twoCore_le hms
  let a := subgroupOfEquivOfLe (show X ≤ J from le_sup_left)
  let : Group.IsPerfect (X.subgroupOf J) := hms.component.2.perfect
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
    (f := a.toMonoidHom) a.surjective
  have hpX : IsPPerfect 2 X := by
    intro D hn hp
    let := hn
    let := hp.isNilpotent
    exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ D)
  have hXN : X ≤ normalizer (N : Set G) :=
    le_sup_left.trans (J.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore J))
  have hcore : X.pCoreIn 2 ≤ N :=
    pCoreAmbient_mono_of_isSubnormalIn X J 2 le_sup_left hms.component.2.subnormal
  have hsig : IsTwoSignalizer X J N := (isTwoSignalizer_iff _ _ _).mpr
    ⟨pCoreIn_le 2 J,isPGroup_pCoreIn 2 J,hXN⟩
  have hcomm := signalizer_commutator_le_pCore X J N le_sup_left
    hms.component.2.subnormal hpX hsig
  intro hz
  have hzero : signalizerModule X N = ⊥ :=
    bot_unique ((signalizerModule_le_intrinsicModule X N hpX hXN hcore hcomm).trans_eq hz)
  have hcentral : X ≤ centralizer (omegaOneCenterAmbient N : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      ((signalizerModule_eq_commutator_omegaCenter X N).symm.trans hzero)
  have hself : J ⊓ centralizer (N : Set G) ≤ N := by
    rintro x ⟨hxJ,hxC⟩
    have hc : (⟨x,hxJ⟩ : J) ∈ centralizer (pCore 2 J : Set J) := by
      intro y hy
      exact Subtype.ext (hxC y (mem_map_of_mem J.subtype hy))
    have hl : centralizer (pCore 2 J : Set J) ≤ pCore 2 J := by
      rw [← hms.fitting]
      exact centralizer_generalizedFitting_le J
    exact mem_map_of_mem J.subtype (hl hc)
  have hRne : R ≠ ⊥ := by
    intro he
    have hn : N = ⊥ := bot_unique (hNR.trans_eq he)
    have hJ : J = ⊥ := by
      apply bot_unique
      rw [←hn]
      intro x hx
      exact hself ⟨hx,by rw [hn]; exact mem_centralizer_iff.mpr (by simp)⟩
    have hX : X = ⊥ := bot_unique (le_sup_left.trans_eq hJ)
    exact hms.component.2.ne_bot (by rw [hX,bot_subgroupOf])
  have homega : omegaOneCenterAmbient R ≤ omegaOneCenterAmbient N := by
    intro z hzR
    obtain ⟨hzR,hz2,hfix⟩ := (mem_omegaOneCenterAmbient_iff R z).mp hzR
    have hn : z ∈ N := hself ⟨mem_sup_right hzR,fun y hy => hfix y (hNR hy)⟩
    exact (mem_omegaOneCenterAmbient_iff N z).mpr ⟨hn,hz2,fun y hy => hfix y (hNR hy)⟩
  let C : Subgroup R := (omega₁ (center R) (p := 2)).map (center R).subtype
  let : (omega₁ (center R) (p := 2)).Characteristic := omega₁_characteristic _
  let : C.Characteristic := inferInstance
  let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr hRne
  have hCne : C ≠ ⊥ := omega_center_ne_bot hpR
  have hCJ : C.map R.subtype ≤ J := (map_subtype_le _).trans le_sup_right
  have hcX : X ≤ centralizer (C.map R.subtype : Set G) :=
    hcentral.trans (centralizer_le homega)
  have hcR : R ≤ centralizer (C.map R.subtype : Set G) := by
    intro r hr z hzC
    exact ((mem_omegaOneCenterAmbient_iff R z).mp hzC).2.2 r hr |>.symm
  have hnorm : J ≤ normalizer (C.map R.subtype : Set G) :=
    (sup_le hcX hcR).trans (Subgroup.centralizer_le_normalizer _)
  exact hCne (hms.characteristic C inferInstance
    ((normal_subgroupOf_iff_le_normalizer hCJ).mpr hnorm))

/-- A nonzero intrinsic module of a perfect subnormal subgroup remains
nonzero in any overgroup containing it. -/
theorem intrinsicModule_ne_bot_of_subnormal
    {X Y : Subgroup G} (hXY : X ≤ Y) (hsub : (X.subgroupOf Y).IsSubnormal)
    (hpX : IsPPerfect 2 X) (hne : intrinsicSignalizerModule X ≠ ⊥) :
    intrinsicSignalizerModule Y ≠ ⊥ := by
  let N := Y.pCoreIn 2
  have hXN : X ≤ normalizer (N : Set G) :=
    hXY.trans (Y.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore Y))
  have hcore : X.pCoreIn 2 ≤ N := pCoreAmbient_mono_of_isSubnormalIn X Y 2 hXY hsub
  have hsig : IsTwoSignalizer X Y N := (isTwoSignalizer_iff _ _ _).mpr
    ⟨pCoreIn_le 2 Y,isPGroup_pCoreIn 2 Y,hXN⟩
  have hcomm := signalizer_commutator_le_pCore X Y N hXY hsub hpX hsig
  have hm := (signalizerModule_ne_bot_iff_intrinsic X N hpX
    (isPGroup_pCoreIn 2 Y) hXN hcore hcomm).mpr hne
  intro hy
  apply hm
  rw [signalizerModule_eq_commutator_omegaCenter]
  change signalizerModule Y N = ⊥ at hy
  rw [signalizerModule_eq_commutator_omegaCenter] at hy
  apply bot_unique
  exact (commutator_mono hXY le_rfl).trans_eq hy

private theorem component_twoPerfect {A : Type*} [Group A] [Finite A]
    {X : Subgroup A} (hX : X.IsCComponent) : IsPPerfect 2 X := by
  let := hX.perfect
  intro N hn hp
  let := hn
  let := hp.isNilpotent
  exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)

namespace PlaneUniquenessPreceding
open Section01 Section03 ChapterA.Section05To06
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- A source MS model of X forces its whole S-orbit outside Mc, including
exchanged components. The actual orbit is not identified with X. -/
theorem linearThree_ms_componentOrbit_not_le_partner
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) {X : Subgroup I} (hX : X.IsCComponent)
    (e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL)
    {R : Subgroup G} (hpR : IsPGroup 2 R) {n : ℕ} {F : Type} [Field F] [Finite F]
    (hms : LinearThreeMSPair KnownSimple.IsKnownSimple (X.map I.subtype) R n F) :
    ¬ planeBlockOrbit T ZS X ≤ Mc := by
  let A := X.map I.subtype
  let Y := planeBlockOrbit T ZS X
  let a := X.equivMapOfInjective I.subtype I.subtype_injective
  let : Group.IsPerfect X := hX.perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  let : Group.IsPerfect Y := conjugateSpanBy_isPerfect A (planeSylow T ZS)
  have hpA : IsPPerfect 2 A := (component_twoPerfect hX).of_surjective a.toMonoidHom a.surjective
  have hAY : A ≤ Y := le_conjugateSpanBy _ _
  have hYI : Y ≤ I := d.blockOrbit_le_escape hI X
  have hAI : (A.subgroupOf I).IsSubnormal := by
    have he : A.subgroupOf I = X := comap_map_eq_self_of_injective I.subtype_injective X
    rw [he]
    exact hX.subnormal
  have hsub : (A.subgroupOf Y).IsSubnormal := hAI.comap (inclusion hYI)
  have hmove : intrinsicSignalizerModule Y ≠ ⊥ :=
    intrinsicModule_ne_bot_of_subnormal hAY hsub hpA
      (linearThreeMS_intrinsicModule_ne_bot hms hpR)
  have hresA : primeToResidual 3 A = ⊤ := by
    let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
    let : IsSimpleGroup (X ⧸ pCore 2 X) := e.isSimpleGroup
    have hd : 3 ∣ Nat.card (X ⧸ pCore 2 X) := by
      rw [Nat.card_congr e.toEquiv,Matrix.PSL3Two.card_PSL]
      decide
    have he := primeToResidual_eq_top_of_simple_quotient 3 2 (pCore 2 X)
      pCore_isPGroup (component_twoPerfect hX) hd
    rw [← map_primeToResidual (p := 3) a,he,map_top_of_surjective _ a.surjective]
  have hresY : primeToResidual 3 Y = ⊤ := by
    let N := (primeToResidual 3 Y).map Y.subtype
    have hAN : A ≤ N := by
      have hh := embedded_primeToResidual_mono 3 hAY
      simpa only [hresA,←MonoidHom.range_eq_map,range_subtype] using hh
    have hSN : planeSylow T ZS ≤ normalizer (N : Set G) :=
      (le_normalizer_conjugateSpanBy A (planeSylow T ZS)).trans
        (normalizer_le_normalizer_characteristic_image Y (primeToResidual 3 Y))
    apply map_injective Y.subtype_injective
    rw [←MonoidHom.range_eq_map,range_subtype]
    exact le_antisymm (map_subtype_le _) (conjugateSpanBy_le hAN hSN)
  intro hout
  exact d.no_normal_perfect_threeResidual horbit hI hYI
    (d.linearThree_componentOrbit_normalized hI hX) hout hresY hmove

/-- The original component also escapes: S already lies in Mc. -/
theorem linearThree_ms_component_not_le_partner
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) {X : Subgroup I} (hX : X.IsCComponent)
    (e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL)
    {R : Subgroup G} (hpR : IsPGroup 2 R) {n : ℕ} {F : Type} [Field F] [Finite F]
    (hms : LinearThreeMSPair KnownSimple.IsKnownSimple (X.map I.subtype) R n F) :
    ¬ X.map I.subtype ≤ Mc := by
  intro hout
  apply d.linearThree_ms_componentOrbit_not_le_partner horbit hI hX e hpR hms
  apply conjugateSpanBy_le hout
  exact ((le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_left).trans
    Mc.le_normalizer

/-- The exact source MS hypotheses discharge escape in the original
parabolic marking, without a nonzero-module callback. -/
theorem linearThree_ms_component_centralizer_parabolic
    (horbit : conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = (pResidual 2 H).map H.subtype ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        conjugateSpanBy ((pResidual 2 H).map H.subtype) Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I) {X : Subgroup I} (hX : X.IsCComponent)
    (e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL)
    {R : Subgroup G} (hpR : IsPGroup 2 R) {n : ℕ} {F : Type} [Field F] [Finite F]
    (hms : LinearThreeMSPair KnownSimple.IsKnownSimple (X.map I.subtype) R n F) :
    IsCoatom ((centralizer (ZS : Set G)).comap (I.subtype.comp X.subtype)) ∧
      X.map I.subtype ⊓ centralizer (ZS : Set G) = X.map I.subtype ⊓ Mc ∧
      X.map I.subtype ⊓ centralizer (ZS : Set G) ≤
        (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS :=
  d.linearThree_component_centralizer_parabolic hI hX e
    (d.linearThree_ms_component_not_le_partner horbit hI hX e hpR hms)

end PlaneUniquenessPreceding
end CFSG.Quasithin.Chapter15.Section02
