module
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.SourceComponent
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.Earlier
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CrossingMarksSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SymplecticBinaryBorel
public import CFSG.Quasithin.Chapter1.Section01Inheritance
public import CFSG.Quasithin.Chapter1.Section01Overgroups
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Original A₆ data for the Frattini argument

Construct every field of the earlier-source interface from the original
Mathieu configuration and its actual A₆ component. The preceding source
results give the full Aut(A₆) quotient, the literal conjugation action with
kernel O₂(H), both center lines, the Borel intersection, and the crossing
element. The original H, K, S, M, T, z, and two-core are retained explicitly.

Even characteristic and the original central Sylow mark also give
characteristic two for C_G(t) ∩ C_G(zᵍ) whenever zᵍ lies in S. This depends
only on the earlier record fields and supplies the action premise used by
the subsequent Frattini argument.

Source: Aschbacher–Smith, Notation 2.5.4 and Lemmas 2.5.5, 2.5.8,
2.5.11–13 and 2.5.21–22, printed pp.554–558 and 565–567.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.A6Shadow.OriginalFrattini
open ComponentRefinement Section05.ComponentSelection Section05.Overcomponents Frattini
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The centralizer intersection for every original z-conjugate lying in S
has characteristic two, from even characteristic and the earlier center marks. -/
theorem conjugate_centralizer_mem_He {κ : GroupClass}
    (d : EarlierSetup κ G) (g : G) (hg : g⁻¹ * d.z * g ∈ d.S) :
    centralizer ({d.t} : Set G) ⊓ centralizer ({g⁻¹ * d.z * g} : Set G) ∈ Chapter1.He G := by
  have hz1 : d.z ≠ 1 := by
    intro hz
    have hh := d.z_order
    rw [hz, orderOf_one] at hh
    omega
  have hne : zpowers d.z ≠ ⊥ := by
    intro he
    exact hz1 (mem_bot.mp (he ▸ mem_zpowers d.z))
  have hpz : IsPGroup 2 (zpowers d.z) := IsPGroup.of_card (n := 1) (by
    simpa only [Nat.card_zpowers, pow_one] using d.z_order)
  have hzHe : centralizer ({d.z} : Set G) ∈ Chapter1.He G := by
    have hn := Chapter1.lemma_1_1_4_3 d.T (d.simpleQTKE.evenCharacteristic d.T) hne hpz (by
      rw [← centerIn_eq_map_center, d.center_t, inf_idem]
      exact hne)
    have hnHe := hn.2.2
    rwa [normalizer_zpowers_eq_centralizer_of_order_two d.z d.z_order] at hnHe
  have he : MulAut.conj g⁻¹ d.z = g⁻¹ * d.z * g := by
    simp only [MulAut.conj_apply, inv_inv]
  have hc := (Theory.Quasithin.centralizer_pCore_le_iff 2
    (CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj g⁻¹) d.z)).mp
      (Chapter1.mem_He_iff.mp hzHe)
  rw [he] at hc
  have hgHe : centralizer ({g⁻¹ * d.z * g} : Set G) ∈ Chapter1.He G :=
    Chapter1.mem_He_iff.mpr hc
  have hpt : IsPGroup 2 (zpowers d.t) := IsPGroup.of_card (n := 1) (by
    simpa only [Nat.card_zpowers, pow_one] using d.t_order)
  have hSH : d.S ≤ d.H := d.generated ▸ le_sup_right
  have htC : d.t ∈ centralizer ({g⁻¹ * d.z * g} : Set G) :=
    mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp (d.h_le_centralizer_t (hSH hg))).symm
  have hh := pCoreIn_selfCentralizing_centralizer hgHe hpt (zpowers_le.mpr htC)
  change centralizer ({g⁻¹ * d.z * g} : Set G) ⊓ centralizer (zpowers d.t : Set G) ∈
    Chapter1.He G at hh
  simpa only [zpowers_eq_closure, centralizer_closure, inf_comm] using hh

/-- The literal original configuration supplies every earlier A₆ Frattini field,
with its ambient data and full involution centralizer retained. -/
theorem original_earlier_setup
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* alternatingGroup (Fin 6)) :
    ∃ d : EarlierSetup KnownSimple.IsKnownSimple G,
      d.H = H ∧ d.K = K ∧ d.S = (S : Subgroup H).map H.subtype ∧
      d.M = M ∧ d.T = c.T ∧ d.z = z ∧ d.SC = twoCore H ∧
      d.H = centralizer ({d.t} : Set G) := by
  classical
  let Y := (S : Subgroup H).map H.subtype
  let D := K.subgroupOf H
  let eD : D ≃* alternatingGroup (Fin 6) := (subgroupOfEquivOfLe c.component_le).trans eK
  let : D.Normal := alternatingGroup.normal_of_component_a6_of_quasithin
    (hG.quasithin.subgroup H) D eD c.component
  have hYN : Y ≤ normalizer (K : Set G) := (map_subtype_le _).trans
    ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance)
  have hOrbit : componentOrbit K Y = K := le_antisymm
    (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hYN) (le_componentOrbit _ _)
  obtain ⟨t, zK, ht, hzK, htC, hCore, hKline, _, hZ, hFour, hZT,
    hHt, _, hSylow, _, hnot⟩ := MathieuSourceSetup.source_central_marks c hG hempty hgen hb
  have htZ : t ∈ centerIn Y := by
    have hh : t ∈ centerIn Y ⊓ twoCore H := hCore.symm ▸ mem_zpowers t
    exact hh.1
  have hSK : centerIn (Y ⊓ K) = zpowers zK := by
    have hh := (MathieuSourceSetup.normal_component_center_split c hG hempty hgen hb).2.2.2
    change centerIn Y ⊓ K = centerIn (Y ⊓ K) at hh
    rw [hOrbit] at hKline
    exact hh.symm.trans hKline
  have hYM : Y ≤ M := c.sylow_lt.le.trans c.sylow_le
  have hout : ¬ D.map H.subtype ≤ M := ((c.hypotheses115 hG).component_inputs D c.component).1
  have hIntersection := alternating_six_intersection_eq_sylow_source c.gamma hempty S hYM D c.component hout eD
  have hKM : K ⊓ M = Y ⊓ K := by
    ext k
    constructor
    · intro hk
      let d : D := ⟨⟨k, c.component_le hk.1⟩, hk.1⟩
      have hd : d ∈ (S : Subgroup H).subgroupOf D :=
        hIntersection ▸ (show d ∈ ((M.subgroupOf H).subgroupOf D) from hk.2)
      exact ⟨mem_map_of_mem H.subtype hd, hk.1⟩
    · intro hk
      exact ⟨hk.2, hYM hk.1⟩
  obtain ⟨x, hxT, hxS, hxN, hx2⟩ :=
    exists_outside_normalizer_square_mem Y (c.T : Subgroup G) c.T.isPGroup' c.sylow_lt
  have hCross := generated_twoCore_disjoint S (MathieuSourceSetup.sourceTuple c)
    ⟨c.component_le, c.component⟩ hgen hxT hxS hxN hx2
  have hxt := (MathieuSourceSetup.source_crossing_on_center c hgen t ht htC htZ hFour).2
    x hxT hxN hxS
  let f : H →* AlternatingSix.ShadowLocal.AutA6 :=
    AlternatingSix.ShadowLocal.conjugationAction D eD
  have hk : f.ker = pCore 2 H := by
    rw [show f = (MulAut.congr eD).toMonoidHom.comp (MulAut.conjNormal : H →* MulAut D) from rfl,
      MonoidHom.ker_comp_of_injective _ _ (MulAut.congr eD).injective]
    exact MathieuSourceSetup.normal_component_conjugation_ker c hG hempty hgen
  obtain ⟨eQ⟩ := MathieuSourceSetup.alternating_six_full_core_quotient c hG hempty hgen hb hstar eK
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply f.range.eq_top_of_card_eq
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
      Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hk).toEquiv]
    exact Nat.card_congr eQ.toEquiv
  have hcompatible (h : H) (k : K) :
      (eK.symm (f h (eK k)) : G) = (h : G) * k * (h : G)⁻¹ := by
    let d : D := (subgroupOfEquivOfLe c.component_le).symm k
    have he : eD d = eK k := by
      simp only [eD, d, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rw [← he, show f = AlternatingSix.ShadowLocal.conjugationAction D eD from rfl,
      AlternatingSix.ShadowLocal.conjugationAction_apply]
    simp only [eD, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val (MulAut.conjNormal_apply h d)
  have hKernel : f.ker = (twoCore H).subgroupOf H := by
    rw [hk]
    exact (comap_map_eq_self_of_injective H.subtype_injective _).symm
  let d : EarlierSetup KnownSimple.IsKnownSimple G := {
    simpleQTKE := hG
    H := H, K := K, S := Y, M := M, T := c.T
    maximalM := c.maximal
    t_le_m := c.sylow_le
    unique_maximal := c.unique
    star := hstar
    even_empty := hempty
    generated := hgen
    normalK := inferInstance
    modelK := eK
    intersection_m := hKM
    sylow := S
    sylow_eq := rfl
    s_le_t := c.sylow_lt.le
    SC := twoCore H
    centralizer_K := MathieuSourceSetup.core_eq_sylow_centralizer c hgen
    core := rfl
    x := x
    x_mem := hxT
    x_normalizes := hxN
    x_outside := hxS
    square_mem := hx2
    disjoint_conjugate := hCross.1
    commuting_conjugate := hCross.2.1
    t := t, z := z, zK := zK
    t_mem := htC
    t_order := ht
    z_order := c.involution
    zK_order := hzK
    center_t := hZT
    center_s := hZ
    center_sc := hCore
    center_sk := hSK
    h_le_centralizer_t := hHt
    centralizer_t_normalizes_K :=
      source_component_normal_in_centralizer_t c hG hempty hgen hb hstar t ht htC htZ
    sylow_centralizer_t := hSylow
    t_not_conjugate_z := by
      intro g he
      apply hnot
      exact (isConj_iff.mpr ⟨g⁻¹, by simpa only [inv_inv] using he⟩).symm
    crossing_t := hxt
    action := f
    action_surjective := hf
    action_compatible := hcompatible
    action_kernel := hKernel }
  refine ⟨d, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact centralizer_eq_of_original_component c hG hempty hgen hb hstar t ht htC htZ eK

end CFSG.Quasithin.Chapter2.A6Shadow.OriginalFrattini
