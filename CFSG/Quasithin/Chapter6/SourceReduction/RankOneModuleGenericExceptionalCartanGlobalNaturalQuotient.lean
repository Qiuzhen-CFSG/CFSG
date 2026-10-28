module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalNaturalDegree
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalInitial
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalNaturalDegree
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldQrc

/-!
# Removing the central kernel from the natural Cartan omega-span

Assume that the original L-span of omega has a natural quotient by its
L-centralizer. A nonzero quotient image of an omega point has trivial
odd-order stabilizer, so the original Cartan acts faithfully on its own
omega-span before the central kernel has been removed. The Sylow subgroup
normalizes this span through the whole Borel, without normalizing the
Cartan itself. Reducedness and the exact two-core identity then construct
Hypothesis 3.1.5 for the literal Cartan/Sylow join.

Above degree two, the source Thompson and common-normal argument makes H
centralize omega: a common normal subgroup would be a nontrivial subgroup
of the zero two-core of the original Cartan/H join. Maximal-local uniqueness
now kills the fixed kernel. The same quotient map becomes a full natural
model, giving degree two or four and small Cartan generation.

This proves the natural fixed-quotient branch on the whole omega-span.
It does not infer that marking from a quotient of only its moved layer;
source alternative selection, other module branches and zero-core
recognition remain with the local-to-global assembly. The two `import all`
lines continue the private numerical/common-normal proof at its existing
boundary; they do not change any public module interface.

Source: Aschbacher--Smith 5.1.2, 5.1.6(2), pp.630,632, and 3.1.7,
pp.575--576, with the Cartan application in 5.2.2, p.647
(`refs/quasithin.pdf`).
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem natural_quotient_omega_not_fixed
    {T : Sylow 2 G} {L : Subgroup G} {n : ℕ}
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n) :
    ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ centralizer (L : Set G) := by
  intro hz
  obtain ⟨F,_,_,_,_,e,m,he⟩ := hm
  let := ZMod.algebra F 2
  have hu : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L ≤
      centralizer (L : Set G) := conjugateSpanBy_le hz
        (L.le_normalizer.trans (normalizer_le_normalizer_centralizer _))
  obtain ⟨v,hv⟩ := exists_ne (1 : Multiplicative (Fin 2 → F))
  obtain ⟨u,rfl⟩ := m.surjective v
  apply hv
  change u ∈ m.quotient.ker
  rw [m.kernel]
  exact hu u.property

omit [Finite G] in
private theorem natural_quotient_odd_point_stabilizer
    {L U : Subgroup G} {n : ℕ} (hm : IsNaturalFixedQuotient L U n)
    {x z : G} (hx : x ∈ L) (ho : Odd (orderOf x))
    (hz : z ∈ U) (hzC : z ∉ centralizer (L : Set G))
    (he : x*z*x⁻¹=z) : x=1 := by
  obtain ⟨F,_,_,_,_,e,m,hm⟩ := hm
  let := ZMod.algebra F 2
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let xL : L := ⟨x,hx⟩
  let zU : U := ⟨z,hz⟩
  have hz0 : (m.quotient zU).toAdd ≠ 0 := by
    intro hzero
    apply hzC
    have hk : zU ∈ m.quotient.ker := hzero
    rwa [m.kernel] at hk
  have heq : U.normalizerMonoidHom ⟨x,m.normalizes hx⟩ zU = zU := Subtype.ext he
  have hfix : (q xL).val.mulVec (m.quotient zU).toAdd = (m.quotient zU).toAdd := by
    have hh := m.equivariant xL zU
    rw [hm,heq] at hh
    exact hh.symm
  have hq : q xL = 1 := by
    by_contra hne
    exact hz0 (Matrix.SL2.odd_power_fixed_eq_zero (q xL) (orderOf x) ho
      (by rw [←map_pow,show xL^orderOf x=1 from Subtype.ext (pow_orderOf_eq_one x),map_one])
      hne (m.quotient zU).toAdd hfix)
  have hcore : xL ∈ pCore 2 L := (QuotientGroup.eq_one_iff xL).mp
    (e.map_eq_one_iff.mp hq)
  have hc := (pCore_isPGroup (p:=2) (G:=L)).orderOf_coprime
    ho.coprime_two_left (⟨xL,hcore⟩ : pCore 2 L)
  have hc' : Nat.Coprime (orderOf x) (orderOf x) := by
    simpa only [Subgroup.orderOf_mk,xL] using hc
  exact orderOf_eq_one_iff.mp (by simpa only [Nat.gcd_self] using hc'.gcd_eq_one)

/-- The literal Cartan span is invariant and faithful even before the natural
quotient's central kernel is known to vanish. -/
theorem Input.natural_quotient_cartan_span
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (c : CartanPair T L H A B)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n) :
    let X := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) A
    A ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
      A ⊓ centralizer (X : Set G) = ⊥ ∧ X ≠ ⊥ := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let X := conjugateSpanBy Z A
  let U := (T : Subgroup G) ⊓ L
  have hZC : Z ≤ centralizer (U : Set G) := fun z hz t ht =>
    ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht.1
  have hUC : U ≤ centralizer (X : Set G) := by
    apply le_centralizer_iff.mp
    exact conjugateSpanBy_le hZC
      ((c.left_le.trans inf_le_right).trans (normalizer_le_normalizer_centralizer _))
  have hUA : U ⊔ A = localBorel T L := c.left_sup_intersection h.sylow_normalizes
  have hspan : conjugateSpanBy Z (U ⊔ A) = X := by
    apply le_antisymm _ (conjugateSpanBy_mono le_rfl le_sup_right)
    exact conjugateSpanBy_le (le_conjugateSpanBy Z A)
      (sup_le (hUC.trans (Subgroup.centralizer_le_normalizer _))
        (le_normalizer_conjugateSpanBy Z A))
  have hTB : (T : Subgroup G) ≤ normalizer (localBorel T L : Set G) :=
    (le_inf h.sylow_normalizes
      ((le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes).trans
        inf_normalizer_le_normalizer_inf |>.trans (normalizer (U : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hTX : (T : Subgroup G) ≤ normalizer (X : Set G) := by
    rw [←hspan,hUA]
    exact normalizes_conjugateSpanBy Z (localBorel T L) (T : Subgroup G)
      ((le_centralizer_iff.mpr (show Z ≤ centralizer (T : Set G) from
        fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2)).trans
          (Subgroup.centralizer_le_normalizer _)) hTB
  obtain ⟨z,hz,hzC⟩ := Set.not_subset.mp (natural_quotient_omega_not_fixed hm)
  have hzX : z ∈ X := le_conjugateSpanBy Z A hz
  have hz0 : z ≠ 1 := fun he => hzC (he ▸ one_mem _)
  refine ⟨sup_le (le_normalizer_conjugateSpanBy Z A) hTX,?_,
    fun he => hz0 (mem_bot.mp (he ▸ hzX))⟩
  apply _root_.eq_bot_iff.mpr
  intro x hx
  apply mem_bot.mpr
  have hoA : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  have ho : Odd (orderOf x) := hoA.of_dvd_nat (by
    rw [←Subgroup.orderOf_mk x hx.1]
    exact orderOf_dvd_natCard _)
  exact natural_quotient_odd_point_stabilizer hm (c.left_le hx.1).1 ho
    (le_conjugateSpanBy Z L hz) hzC
    (mul_inv_eq_iff_eq_mul.mpr ((hx.2 z hzX).symm))

/-- The original Cartan omega-span is reduced in AT before killing the fixed kernel. -/
theorem Input.natural_quotient_cartan_span_reduced
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (c : CartanPair T L H A B)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n) :
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    conjugateSpanBy Z A ∈ reducedFamily (A ⊔ (T : Subgroup G)) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let V := conjugateSpanBy Z A
  let J := A ⊔ (T : Subgroup G)
  have hg := h.natural_quotient_cartan_span c hm
  have hn : J ≤ normalizer (V : Set G) := hg.1
  have hjoin : conjugateSpanBy Z J = V := le_antisymm
    (conjugateSpanBy_le (le_conjugateSpanBy Z A) hn)
    (conjugateSpanBy_mono le_rfl le_sup_left)
  have hZT : Z ≤ (T : Subgroup G) := fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hZJ : Z ≤ J := hZT.trans le_sup_right
  have hVJ : V ≤ J := hjoin ▸ conjugateSpanBy_le_self hZJ
  have hu := LocalOmega.span_elementary_le_sylow T L (h.qtke.evenCharacteristic T)
    h.maximal_local.1 h.sylow_normalizes
  let := hu.1
  have hVU : V ≤ conjugateSpanBy Z L :=
    conjugateSpanBy_mono le_rfl (c.left_le.trans inf_le_left)
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_injective
    (inclusion hVU) (inclusion_injective hVU)
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hz : omegaOneCenterAmbient (S : Subgroup J) = Z.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [←omegaOneCenterAmbient_map_injective J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le hZJ]
    congr 1
    exact map_subgroupOf_eq_of_le le_sup_right
  have hclosure : normalClosure (omegaOneCenterAmbient (S : Subgroup J) : Set J) = V.subgroupOf J := by
    rw [hz,normalClosure_subgroupOf_eq_conjugateSpanBy _ J hZJ,hjoin]
  let : IsElementaryAbelian 2 (V.subgroupOf J) := IsElementaryAbelian.subgroupOf hVJ
  let : IsMulCommutative (normalClosure (omegaOneCenterAmbient (S : Subgroup J) : Set J)) := by
    rw [hclosure]
    infer_instance
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (S : Subgroup J)) :=
    omegaOneCenterAmbient_elementaryAbelian _
  have hr := isPReduced_normalClosure_of_sylow_central S
    (omegaOneCenterAmbient (S : Subgroup J))
    (fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
    (fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2)
  rw [hclosure] at hr
  exact ⟨hVJ,inferInstance,hr.normal,hr.quotient_pCore_eq_bot⟩


/-- Source 3.1.5 on the original Cartan span, retaining the natural quotient kernel. -/
theorem Input.natural_quotient_cartan_qrc_hypotheses
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hz : (A ⊔ H).pCoreIn 2 = ⊥) :
    Chapter3.QrcHypotheses T (normalizer (L : Set G))
      (A ⊔ (T : Subgroup G)) H
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) A) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let X := conjugateSpanBy Z A
  let J := A ⊔ (T : Subgroup G)
  have hg := h.natural_quotient_cartan_span c hm
  have hr := h.natural_quotient_cartan_span_reduced c hm
  let := hr.2.1
  have hJN : J ≤ normalizer (X : Set G) := reduced_normalizes hr
  have hcore := reduced_torus_centralizer hr
    (torus_join_card c h.sylow_normalizes h.linear le_rfl) hg.2.1
  refine ⟨le_sup_right,
    sup_le (c.left_le.trans (inf_le_left.trans L.le_normalizer)) h.sylow_normalizes,
    hH,hr.1,hJN,hr.2.1,?_,hcore,Or.inl (cartan_residual_normalized h hH c hz)⟩
  · exact Chapter3.Section02.internalActionImage_core_of_reduced J X hr.1 hJN
      (show IsPReduced 2 (X.subgroupOf J) from
        ⟨hr.2.2.choose,IsElementaryAbelian.subgroupOf hr.1,hr.2.2.choose_spec⟩)

private theorem natural_quotient_cartan_qrc_configuration
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hz : (A ⊔ H).pCoreIn 2 = ⊥) :
    ChapterD.QRCConfiguration (A ⊔ (T : Subgroup G)) H (T : Subgroup G)
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) A) := by
  let hq := h.natural_quotient_cartan_qrc_hypotheses hH c hm hz
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  apply hq.toQRCConfiguration
  rintro ⟨N,hNc,hN,hn⟩
  have hNT : N ≤ (T : Subgroup G) := hNc.trans (hq.core_eq_centralizer ▸ inf_le_left)
  have hgen : Chapter3.generated (A ⊔ (T : Subgroup G)) H = A ⊔ H := by
    rw [Chapter3.generated_eq_sup,sup_assoc,sup_eq_right.mpr hTH]
  have hnorm : A ⊔ H ≤ normalizer (N : Set G) := by
    simpa only [hgen] using (Chapter3.normalIn_iff_le_normalizer.mp hn).2
  have hcore := le_pCoreIn_of_normalizes (T.isPGroup'.to_le hNT)
    (hNT.trans (hTH.trans le_sup_right)) hnorm
  exact hN (bot_unique (hz ▸ hcore))

/-- The source 3.1.7 common-normal argument forces H to centralize omega
above degree two, using the natural quotient without assuming a splitting. -/
theorem Input.natural_quotient_cartan_omega_centralizes
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hn : 2 < n) (hz : (A ⊔ H).pCoreIn 2 = ⊥) : H ≤ omegaCentralizer T := by
  have hZ : omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype := by
    by_contra hZ
    have hjW := h.thompson_moves_of_noncentral_omega hH hZ
    obtain hJN | ⟨he,_⟩ := h.borel_thompson_or_degree_two hjW
    swap
    · omega
    let X := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) A
    let J := A ⊔ (T : Subgroup G)
    let hq := h.natural_quotient_cartan_qrc_hypotheses hH c hm hz
    let d := natural_quotient_cartan_qrc_configuration h hH c hm hz
    have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
      sSup_le fun _ hE => hE.1
    have hJcore : elementaryAbelianMaxJ (T : Subgroup G) ≤ J.pCoreIn 2 :=
      le_pCoreIn_of_normalizes (T.isPGroup'.to_le hJT) (hJT.trans le_sup_right)
        ((sup_le_sup_right c.left_le _).trans hJN)
    have hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (X : Set G) :=
      hJcore.trans (hq.core_eq_centralizer ▸ inf_le_right)
    let S := T.subtype (show (T : Subgroup G) ≤ H from hH.1.1.2)
    let Z := omegaOneCenterAmbient (S : Subgroup H)
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    have hU : IsPReduced 2 U := hq.sylowOmega_reduced (h.qtke.evenCharacteristic T)
    let := hU.normal
    have hZT : omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) :=
      fun _ hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1
    have hzmap : Z.map H.subtype = omegaOneCenterAmbient (T : Subgroup G) := by
      rw [←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective]
      congr 1
      exact map_subgroupOf_eq_of_le hH.1.1.2
    have hZU : Z ≤ U := by
      intro z hz
      apply le_conjugateSpanBy
      exact hzmap ▸ mem_map_of_mem H.subtype hz
    have hjmap : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
        elementaryAbelianMaxJ (T : Subgroup G) := by
      rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
      congr 1
      exact map_subgroupOf_eq_of_le hH.1.1.2
    have hJn : ¬ (elementaryAbelianMaxJ (S : Subgroup H)).Normal := by
      intro hnormal
      let := hnormal
      have hnorm := (elementaryAbelianMaxJ (S : Subgroup H)).le_normalizer_map H.subtype
      rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,hjmap] at hnorm
      obtain ⟨N,hNR,hN,hnN⟩ := hq.common_normal_of_thompson_normal h.maximal hJ hnorm
      exact hN (d.no_common_normal N hNR (by
        simpa only [Chapter3.generated_eq_sup] using (Chapter3.normalIn_iff_le_normalizer.mp hnN).2))
    have hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤ := by
      obtain ⟨K,⟨hK,hTK⟩,hk⟩ := Chapter3.HStar.unique_maximal_subgroup T h.sylow_normalizes hH
      have hSK : (S : Subgroup H) ≤ K := by
        intro t ht
        obtain ⟨k,hk,he⟩ := hTK ht
        exact H.subtype_injective he ▸ hk
      refine ⟨hSK.trans_lt hK.lt_top,K,⟨hSK,hK.covBy_top⟩,?_⟩
      intro C hC
      apply hk C
      exact ⟨hC.2.isCoatom,fun t ht => ⟨⟨t,hH.1.1.2 ht⟩,hC.1 ht,rfl⟩⟩
    have hj := thompson_not_centralizes_of_unique_maximal S U Z hZU
      (fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2)
      (fun hc => hZ (by rw [←hzmap]; exact map_mono hc)) hu hJn
    have hRne : J.pCoreIn 2 ≠ ⊥ := by
      intro he
      have hX : X = ⊥ := bot_unique (d.module_le_core.trans_eq he)
      exact (h.natural_quotient_cartan_span c hm).2.2 hX
    have hp := hstar_minimalParabolic_of_generation_gt_one h.sylow_normalizes hH hgen
    obtain ⟨N,hNR,hN,hnN⟩ := hq.common_normal_of_residual_sylow
      (Chapter3.source_common_normal_knownSimple h.qtke T) hRne
      (residual_sylow_of_reduced_module hq h.qtke hp hJ U hU hj)
    exact hN (d.no_common_normal N hNR (by
      simpa only [Chapter3.generated_eq_sup] using (Chapter3.normalIn_iff_le_normalizer.mp hnN).2))
  intro x hx z hz'
  obtain ⟨a,ha,rfl⟩ := hZ hz'
  exact (congrArg H.subtype ((mem_center_iff.mp ha) ⟨x,hx⟩)).symm


/-- Above degree two, the original central quotient has trivial kernel.
The same quotient marking therefore supplies coordinates on the whole omega-span. -/
theorem Input.natural_quotient_cartan_model
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hn : 2 < n) (hz : (A ⊔ H).pCoreIn 2 = ⊥) :
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    U ⊓ centralizer (L : Set G) = ⊥ ∧ IsNaturalModule L U n := by
  have hHC := h.natural_quotient_cartan_omega_centralizes hH hgen c hm hn hz
  have hLC : ¬ L ≤ omegaCentralizer T := fun hc =>
    natural_quotient_omega_not_fixed hm (le_centralizer_iff.mp hc)
  have hf := (h.omega_span_input hLC).reduced_fixed_eq_bot_of_outside_centralizes hH hHC
  exact ⟨hf,hm.natural_of_fixed_eq_bot hf⟩

/-- The source natural fixed quotient on the original omega-span gives
small Cartan generation without a splitting or centralization premise. -/
theorem Input.natural_quotient_cartan_degree_and_smallGeneration
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B)
    (hm : IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hz : (A ⊔ H).pCoreIn 2 = ⊥) :
    (n = 2 ∨ n = 4) ∧ CartanSmallGeneration A H n := by
  by_cases hn : n = 2
  · exact ⟨Or.inl hn,h.cartanSmallGeneration_of_degree_two_or_four hH c (Or.inl hn)⟩
  have hn2 : 2 < n := by have := h.exponent; omega
  exact h.natural_cartan_degree_and_smallGeneration hH hgen c
    (h.natural_quotient_cartan_model hH hgen c hm hn2 hz).2 hz

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
