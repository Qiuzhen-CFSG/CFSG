module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.Factors
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.Residuals
public import Theory.GroupTheory.SylowCoreRestriction

/-!
# Centralizing the distinguished plane in the reducible case

Reducibility puts O₂(H) in S. Since H and KcT contain the same Sylow
subgroup, O₂(KcT) lies in O₂(H). The self-centralizing core of KcT
therefore contains ZS in its omega-center. If Kc is a component orbit,
the empty faithful-component family makes its intrinsic signalizer
module trivial. The signalizer comparison then makes Kc centralize ZS.
The other orbit alternative is already the earlier centralization of K.

Thus the literal Kc lies in MI = Mc ∩ I and equals O^{3′}(MI).
Only the genuine 15.2.12(2) orbit alternative remains explicit, with
its earlier-source producer qt-e-152-plane-geometry and final discharge
in qt-e-152-plane-uniqueness. The binary application is in PairApplications.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.2.21(1), printed p.1114; refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
open Section01 Section03 ChapterA.Section04 Chapter1.Section02.Adequate
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- The actual orbit span centralizes ZS when the S-action on K/O₂(K) is reducible. -/
theorem orbit_centralizes_of_reducible
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I)
    (hnot : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H)) :
    smallActionKc H Mc ≤ centralizer (ZS : Set G) := by
  rcases horbit with he | ⟨L,hL,he⟩
  · exact he ▸ d.residual_centralizes
  let Kc := smallActionKc H Mc
  let J := Kc ⊔ (T : Subgroup G)
  let Q := J.pCoreIn 2
  have hTMc : (T : Subgroup G) ≤ Mc :=
    d.geometry.outside.1.1.2.trans d.geometry.in_partner
  have hKMc : smallActionK H ≤ Mc := (map_subtype_le _).trans d.geometry.in_partner
  have hKcMc : Kc ≤ Mc := conjugateSpanBy_le_self hKMc
  have hJMc : J ≤ Mc := sup_le hKcMc hTMc
  have hJK : J ≤ normalizer (Kc : Set G) :=
    sup_le Kc.le_normalizer (hTMc.trans (le_normalizer_conjugateSpanBy _ _))
  have hJQ : J ≤ normalizer (Q : Set G) := J.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hKcQ : Kc ≤ normalizer (Q : Set G) := le_sup_left.trans hJQ
  have hQKc : Q ≤ normalizer (Kc : Set G) := (pCoreIn_le 2 J).trans hJK
  have hHle : H ≤ J := by
    rw [← d.residual_sup_sylow]
    exact sup_le_sup_right (le_conjugateSpanBy _ _) _
  have hQS : Q ≤ smallActionS T ZS :=
    (pCoreIn_le_of_sylow_le T d.geometry.outside.1.1.2 hHle).trans
      (core_le_planeSylow_of_reducible d hI hnot)
  have hMc : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hsource.partner ▸ Set.mem_singleton Mc).1
  have hMcHe : Mc ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr
    (hsource.ambient.evenCharacteristic T Mc hMc hTMc)
  have hQMcT : Mc.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTMc] using
      pCoreIn_le_sylow Mc (T.subtype hTMc)
  have hJne : J ≠ ⊥ := by
    intro hz
    apply d.residual_not_le
    exact ((map_subtype_le _).trans (hHle.trans hz.le)).trans bot_le
  have hJHe : J ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_4_4 hJne hJMc hMcHe
      (inf_le_left.trans (hQMcT.trans le_sup_right))
  have hZQ : ZS ≤ centralizer (Q : Set G) :=
    le_centralizer_iff.mp (hQS.trans inf_le_right)
  have hZJ : ZS ≤ J := by
    intro z hz
    rw [d.omega_center] at hz
    exact (show (T : Subgroup G) ≤ J from le_sup_right)
      ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1.1
  have hZomega : ZS ≤ omegaOneCenterAmbient Q := by
    intro z hz
    have hpow := ((mem_omegaOneCenterAmbient_iff _ _).mp (d.omega_center ▸ hz)).2.1
    exact (mem_omegaOneCenterAmbient_iff Q z).mpr
      ⟨hJHe ⟨hZJ hz,hZQ hz⟩,hpow,hZQ hz⟩
  have hmod : intrinsicSignalizerModule Kc = ⊥ := by
    by_contra hn
    have hfaith : L ∈ MainForward.faithfulLocalComponents T :=
      (mem_faithfulLocalComponents_iff_module T (hsource.ambient.evenCharacteristic T)).mpr
        ⟨hL,Chapter1.Terminal.intrinsicModule_ne_bot_of_orbit hL (he ▸ hn)⟩
    rw [hsource.empty] at hfaith
    exact hfaith
  have hpKc : IsPPerfect 2 Kc := by
    rw [show Kc = componentOrbit L (T : Subgroup G) from he]
    let := Chapter1.mem_L_isPerfect hL
    let : Group.IsPerfect (componentOrbit L (T : Subgroup G)) := isPerfect_iSup_conjugates L T
    intro N hn hp
    let := hn
    let := hp.isNilpotent
    exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ N)
  have hcore : Kc.pCoreIn 2 ≤ Q := pCoreIn_mono_of_normalizes le_sup_left hJK
  have hcomm : ⁅Kc,Q⁆ ≤ Kc.pCoreIn 2 := by
    rw [commutator_comm]
    exact le_pCoreIn_of_normalizes
      ((isPGroup_pCoreIn 2 J).to_le (le_normalizer_iff_commutator_le_left.mp hKcQ))
      (le_normalizer_iff_commutator_le_right.mp hQKc)
      (normalizer_commutator_ge_right Q Kc)
  have hzero : signalizerModule Kc Q = ⊥ := by
    by_contra hn
    exact ((signalizerModule_ne_bot_iff_intrinsic Kc Q hpKc (isPGroup_pCoreIn 2 J)
      hKcQ hcore hcomm).mp hn) hmod
  rw [signalizerModule_eq_commutator_omegaCenter] at hzero
  exact (commutator_eq_bot_iff_le_centralizer.mp hzero).trans (centralizer_le hZomega)

/-- The corrected residual conclusion of 15.2.21(1), on Mc ∩ I. -/
theorem orbit_residual_MI_of_reducible
    (horbit : smallActionKc H Mc = smallActionK H ∨
      ∃ L : Subgroup G, L ∈ Chapter1.L G T ∧
        smallActionKc H Mc = componentOrbit L (T : Subgroup G))
    (hI : PlaneEscapes Mc ZS I)
    (hnot : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H)) :
    smallActionKc H Mc =
      (primeToResidual 3 (Mc ⊓ I : Subgroup G)).map (Mc ⊓ I).subtype :=
  orbit_eq_residual_MI_of_centralizes d hI (orbit_centralizes_of_reducible d horbit hI hnot)

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
