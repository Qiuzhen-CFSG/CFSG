module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ComponentActors
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CoreContainment

/-!
# The three-core's action on the original component quotient

The full three-core preimage B lies in M = N_G(L). Let X be the
two-residual of its kernel on L/O₂(L). The original Sylow subgroup
normalizes X. An escaping C-component centralizes the three-core in the
star quotient; two-perfect normalizer lifting through O₂(I) shows that
it normalizes X. If X were nontrivial, ambient normalizer control would
put that component in M, a contradiction. Thus the action kernel is a
two-group. Since |Aut(L₃(2))| = 336 is not divisible by nine, the actual
three-core has order at most three.

The component used here is obtained from the already proved nonsolvability
of every original local. Its ordinary quasisimple star image is supplied
by ComponentQuotients, independently of the odd-core equality.

Source: Aschbacher–Smith, 14.7.27, printed pp.1054–1055, using the
normalizer control of 14.5.20 and the independent 14.7.29 route,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual three-core preimage acts on L/O₂(L) with a two-group kernel.
An escaping component rules out a nontrivial kernel two-residual. -/
theorem local_threeCore_action_kernel_two
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    let hBM := (local_threeCore_preimage_control d h hab structural previous faithful earlier I hI).1
    IsPGroup 2 (((normalizerQuotientAction L (pCore 2 L)).comp (inclusion hBM)).ker) := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let N := (pCore 3 (HStar I)).comap q
  let B := N.map I.subtype
  let M := normalizer (L : Set G)
  let a := normalizerQuotientAction L (pCore 2 L)
  let C := a.ker.map M.subtype
  let E := B ⊓ C
  let X := (pResidual 2 E).map E.subtype
  have hBI : B ≤ I := map_subtype_le N
  have hBM : B ≤ M :=
    (local_threeCore_preimage_control d h hab structural previous faithful earlier I hI).1
  have hIB : I ≤ normalizer (B : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      N.le_normalizer_map I.subtype
  have hMC : M ≤ normalizer (C : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      a.ker.le_normalizer_map M.subtype
  have hTE : (T : Subgroup G) ≤ normalizer (E : Set G) :=
    (le_inf ((F.sylow_le_of_mem_Hz hI).trans hIB)
      ((h.sylow_normalizes structural).trans hMC)).trans inf_normalizer_le_normalizer_inf
  have hTX : (T : Subgroup G) ≤ normalizer (X : Set G) :=
    hTE.trans (normalizer_le_normalizer_characteristic_image E (pResidual 2 E))
  have hXB : X ≤ B := (map_subtype_le _).trans inf_le_left
  have hXC : X ≤ C := (map_subtype_le _).trans inf_le_right
  have hXI : X ≤ I := hXB.trans hBI
  have hXM : X ≤ M := hXB.trans hBM
  have hcomm : ⁅L,X⁆ ≤ L.pCoreIn 2 := by
    apply commutator_le_of_normalizerQuotientAction_eq_one L X (pCore 2 L) hXM
    intro x
    obtain ⟨c,hc,he⟩ := hXC x.property
    have hh : c = inclusion hXM x := Subtype.ext he
    exact hh ▸ hc
  obtain ⟨K,hK,_,hout⟩ := local_exists_quasisimple_component d h hab structural previous
    faithful earlier I hI
  have hcK := local_component_star_isComponent h hab structural previous faithful I hI K hK
  let : IsQuasisimple (K.map q) := hcK.2
  let : IsSimpleGroup ((K.map q) ⧸ center (K.map q)) := IsQuasisimple.simple
  let : Nontrivial (K.map q) := (QuotientGroup.mk'_surjective (center (K.map q))).nontrivial
  have hKP : ⁅K.map q,pCore 3 (HStar I)⁆ = ⊥ := by
    rcases hcK.normal_dichotomy (pCore 3 (HStar I)) with hp | hc
    · exact (Group.IsPerfect.not_isNilpotent (K.map q) (pCore_isPGroup.to_le hp).isNilpotent).elim
    · exact hc
  have hXsub : (X.subgroupOf I).map q ≤ pCore 3 (HStar I) := by
    have hXN : X.subgroupOf I ≤ N := by
      simpa only [B,subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using
        subgroupOf_mono I hXB
    exact (map_mono hXN).trans (by rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)])
  have hKcent : K.map q ≤ centralizer ((X.subgroupOf I).map q : Set (HStar I)) := by
    intro k hk x hx
    exact (commutator_eq_bot_iff_le_centralizer.mp hKP) hk x (hXsub hx)
  have hKX : K.map q ≤ normalizer ((X.subgroupOf I).map q : Set (HStar I)) :=
    hKcent.trans (Subgroup.centralizer_le_normalizer _)
  have hXperfect : IsPPerfect 2 (X.subgroupOf I) :=
    (isPPerfect_embedded_pResidual 2 E).of_surjective
      (subgroupOfEquivOfLe hXI).symm.toMonoidHom (subgroupOfEquivOfLe hXI).symm.surjective
  have hQX : q.ker ≤ normalizer (X.subgroupOf I : Set I) := by
    rw [QuotientGroup.ker_mk']
    apply (pCore_isPGroup.le_sylow_of_normal (T.subtype (F.sylow_le_of_mem_Hz hI))).trans
    rw [←subgroupOf_normalizer_eq hXI]
    exact fun x hx => hTX hx
  have hKX' : K ≤ normalizer (X.subgroupOf I : Set I) := by
    rw [←comap_normalizer_map_of_pPerfect q (X.subgroupOf I) hXperfect
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) hQX]
    exact map_le_iff_le_comap.mp hKX
  have hKXG : K.map I.subtype ≤ normalizer (X : Set G) := by
    rw [←subgroupOf_normalizer_eq hXI] at hKX'
    rintro _ ⟨k,hk,rfl⟩
    exact hKX' hk
  have hXbot : X = ⊥ := by
    by_contra hn
    exact hout (hKXG.trans (local_twoPerfect_core_commutator_normalizer h structural I hI
      X hXI (isPPerfect_embedded_pResidual 2 E) hn hTX hcomm))
  have hRbot : pResidual 2 E = ⊥ :=
    (map_eq_bot_iff_of_injective _ E.subtype_injective).mp hXbot
  have hE2 : IsPGroup 2 E := (isPGroup_quotient_pResidual 2).of_equiv
    ((QuotientGroup.quotientMulEquivOfEq hRbot).trans QuotientGroup.quotientBot)
  let f := a.comp (inclusion hBM)
  have he : f.ker.map B.subtype = E := by
    ext x
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact ⟨b.property,⟨inclusion hBM b,hb,rfl⟩⟩
    · rintro ⟨hx,⟨c,hc,he⟩⟩
      refine ⟨⟨x,hx⟩,?_,rfl⟩
      change a (inclusion hBM ⟨x,hx⟩) = 1
      have hh : inclusion hBM ⟨x,hx⟩ = c := Subtype.ext he.symm
      exact hh.symm ▸ hc
  have hk : IsPGroup 2 (f.ker.map B.subtype) := he.symm ▸ hE2
  exact hk.of_equiv (equivMapOfInjective f.ker B.subtype B.subtype_injective).symm

private theorem point_quotient_aut_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) :
    Nat.card (MulAut (L ⧸ pCore 2 L)) = 336 := by
  let := h.chosen.elementary
  let e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL :=
    h.naturalMarking.quotientEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
  rw [Nat.card_congr (MulAut.congr (e.trans Matrix.PSL3Two.equiv)).toEquiv]
  exact Matrix.PSL3Two.Automorphisms.card_aut

/-- The actual three-core has order at most three. Its full preimage's
quotient action has a two-group kernel, and 9 does not divide |Aut(L₃(2))|. -/
theorem local_threeCore_card_le_three
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    Nat.card (pCore 3 (HStar I)) ≤ 3 := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let N := (pCore 3 (HStar I)).comap q
  let B := N.map I.subtype
  have hBM : B ≤ normalizer (L : Set G) :=
    (local_threeCore_preimage_control d h hab structural previous faithful earlier I hI).1
  let f := (normalizerQuotientAction L (pCore 2 L)).comp (inclusion hBM)
  have hk : IsPGroup 2 f.ker :=
    local_threeCore_action_kernel_two d h hab structural previous faithful earlier I hI
  have hdiv : Nat.card (pCore 3 (HStar I)) ∣ Nat.card B := by
    rw [card_map_of_injective I.subtype_injective]
    have hh := card_map_dvd N q
    rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hh
  have hnine : ¬ 9 ∣ Nat.card B := by
    intro hh
    rw [card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at hh
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    rw [hn] at hh
    have hcop : Nat.Coprime 9 (2 ^ n) := (by decide : Nat.Coprime 9 2).pow_right n
    have h9 : 9 ∣ Nat.card f.range := hcop.dvd_of_dvd_mul_right hh
    have ha := h9.trans f.range.card_subgroup_dvd_card
    rw [point_quotient_aut_card h] at ha
    norm_num at ha
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := HStar I)).exists_card_eq
  have hlt : n < 2 := by
    by_contra hh
    have hp : 3 ^ 2 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
    exact hnine ((hn.symm ▸ hp).trans hdiv)
  rw [hn]
  interval_cases n <;> norm_num

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
