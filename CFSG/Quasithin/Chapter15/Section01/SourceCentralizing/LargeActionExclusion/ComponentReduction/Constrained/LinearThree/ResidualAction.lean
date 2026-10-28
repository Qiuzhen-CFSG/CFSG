module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.LinearThree.Setup
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.ResidualControl
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Theory.GroupTheory.PResidual.TwoKernelComparison
public import Theory.GroupTheory.CComponent.CentralizerMovement
public import Theory.SpecificGroups.PSL3Two.InvolutionFixer
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwoSource

/-!
# The actual second-parabolic residual in the binary SL₃ branch

The original faithful centralizer quotient has two-residual of order three.
Every noncentral two-perfect subgroup therefore has the same movement and
fixed subgroup. Applied to Y₀=O²(M∩L), this places V₂ in Z(O₂(Y₀)), computes
the action index, and transports the action to the literal conjugate Y₀ᵗ.
Original 1.2.1(3), in N_G(V₁), makes that conjugate normalize L.

The remaining block calculation is reduced without assuming that the whole
center of O₂(Y₀) lies in U(L): either V₂ embeds into the natural module and
has order four, or its image modulo O₂(L) contains an involution. In the
latter case the exchanged residual centralizes the actual core quotient.
Both plane rows are retained until the proved cardinality bound applies.

Source: Aschbacher--Smith 15.1.24(2)--(3), printed p.1101.
The constrained-recognition owner retains the remaining block calculation
and final exclusion; this module does not assert that exclusion.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The literal second-parabolic residual acts nontrivially on the moving plane. -/
theorem ExchangedSource.linearThreeY_not_centralizes
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hTM : (T : Subgroup G) ≤ M) (h : PreparedChosenModule T M V)
    (a : d.ConstrainedL3Alternative) :
    ¬ d.nineMovingPlane ≤ centralizer (d.linearThreeY : Set G) := by
  have hVS : d.nineMovingPlane ≤ d.S := by
    obtain ⟨t,ht,htS⟩ := s.exchange_exists
    have hf := map_mono (f := (MulAut.conj t).toMonoidHom)
      ((d.fixedPlane_le_sylow_cubicCentralizer hTM h).trans inf_le_left)
    rw [(s.exchanges t ht htS).1] at hf
    have hn : (T : Subgroup G) ≤ normalizer (d.S : Set G) := by
      let := s.sylow_normal
      exact le_normalizer_of_normal_subgroupOf d.S_le_T
    have he : d.S.map (MulAut.conj t).toMonoidHom = d.S :=
      mem_normalizer_iff_map_conj_eq.mp (hn ht)
    exact hf.trans he.le
  intro hc
  have hr : (primeToResidual 3 (M ⊓ d.L : Subgroup G)).map (M ⊓ d.L).subtype ≤
      d.linearThreeY := map_mono primeToResidual_three_le_twoResidual
  have hVL := ((le_inf hVS (hc.trans (centralizer_le hr))).trans a.centralizers.le).trans
    inf_le_right
  exact s.moving_noncentral (by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hVL)

/-- A nontrivial two-perfect actor in the original marked centralizer has the
same action as its entire two-residual, whose faithful image has order three. -/
theorem PreExclusionSource.moving_of_noncentral_twoPerfect
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (sp : d.PreExclusionSource h.normalized 3)
    {B : Subgroup G} (hBC : B ≤ M ⊓ d.G1) (hB : IsPPerfect 2 B)
    (hne : ¬ B ≤ centralizer (V : Set G)) :
    ⁅V,B⁆ = d.nineMovingPlane ∧ ⁅d.nineMovingPlane,B⁆ = d.nineMovingPlane ∧
      B.pCoreIn 2 ≤ centralizer (V : Set G) ∧
      (centralizer (V : Set G)).relIndex B = 3 ∧
      V ⊓ centralizer (B : Set G) = d.nineFixedPlane := by
  let C := M ⊓ d.G1
  let N := M ⊓ centralizer (V : Set G)
  let K := N.subgroupOf C
  let : K.Normal := caseI_module_centralizer_normal (Z1 := d.Z1) h.normalized
  let q := QuotientGroup.mk' K
  let A := B.subgroupOf C
  let R := pResidual 2 (C ⧸ K)
  have hNC : N ≤ C := inf_le_inf_left M (centralizer_le (d.Z1_le_fixed.trans inf_le_left))
  have hAperfect : IsPPerfect 2 A := hB.of_surjective
    (subgroupOfEquivOfLe hBC).symm.toMonoidHom (subgroupOfEquivOfLe hBC).symm.surjective
  have hAR : A.map q ≤ R := (map_mono (le_pResidual_of_isPPerfect A hAperfect)).trans
    (map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective K)).le
  have hAne : A.map q ≠ ⊥ := by
    intro he
    have hker := (Subgroup.map_eq_bot_iff A (f := q)).mp he
    apply hne
    intro b hb
    have hk : (⟨b,hBC hb⟩ : C) ∈ K := (QuotientGroup.eq_one_iff _).mp (hker hb)
    exact hk.2
  have hcard : Nat.card R = 3 := sp.residual_card
  let : Fact (Nat.card R).Prime := ⟨hcard ▸ Nat.prime_three⟩
  have himage : A.map q = R := by
    rcases ((A.map q).subgroupOf R).eq_bot_or_eq_top_of_prime_card with he | he
    · have hh := congrArg (map R.subtype) he
      rw [map_subgroupOf_eq_of_le hAR,Subgroup.map_bot] at hh
      exact (hAne hh).elim
    · have hh := congrArg (map R.subtype) he
      rw [map_subgroupOf_eq_of_le hAR,←MonoidHom.range_eq_map,range_subtype] at hh
      exact hh
  have hsame : A.map q = (pResidual 2 C).map q :=
    himage.trans (map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective K)).symm
  have hs := congrArg (fun P => (P.comap q).map C.subtype) hsame
  simp only [comap_map_eq, Subgroup.map_sup, show q.ker = K from QuotientGroup.ker_mk' K,
    A,K,
    map_subgroupOf_eq_of_le hNC] at hs
  rw [map_subgroupOf_eq_of_le (show B ≤ C from hBC)] at hs
  have hnB : B ≤ normalizer (V : Set G) := (hBC.trans inf_le_left).trans h.normalized
  have hnR : d.nineResidual ≤ normalizer (V : Set G) :=
    ((map_subtype_le _).trans inf_le_left).trans h.normalized
  have hmove : ⁅V,B⁆ = d.nineMovingPlane := by
    change ⁅V,B⁆ = ⁅V,d.nineResidual⁆
    calc
      ⁅V,B⁆ = ⁅V,N ⊔ B⁆ := commutator_eq_of_centralizing_sup rfl inf_le_right hnB
      _ = ⁅V,N ⊔ d.nineResidual⁆ := by
        rw [sup_comm N B, hs, sup_comm]
        rfl
      _ = ⁅V,d.nineResidual⁆ :=
        (commutator_eq_of_centralizing_sup rfl inf_le_right hnR).symm
  let f := q.comp (inclusion hBC)
  have hr : f.range = R := by
    rw [MonoidHom.range_comp, inclusion_range]
    exact himage
  have hkf : f.ker = (centralizer (V : Set G)).subgroupOf B := by
    ext x
    change q (inclusion hBC x) = 1 ↔ (x : G) ∈ centralizer (V : Set G)
    exact ⟨fun hx => ((QuotientGroup.eq_one_iff _).mp hx).2,
      fun hx => (QuotientGroup.eq_one_iff _).mpr ⟨(hBC x.property).1,hx⟩⟩
  have hi : (centralizer (V : Set G)).relIndex B = 3 := by
    change ((centralizer (V : Set G)).subgroupOf B).index = 3
    rw [←hkf,index_ker,hr]
    exact hcard
  have hfix : V ⊓ centralizer (B : Set G) = d.nineFixedPlane := by
    change V ⊓ centralizer (B : Set G) = V ⊓ centralizer (d.nineResidual : Set G)
    have hNV : V ≤ centralizer (N : Set G) := le_centralizer_iff.mp inf_le_right
    change B ⊔ N = d.nineResidual ⊔ N at hs
    have h1 : V ⊓ centralizer (B : Set G) ≤ centralizer ((B ⊔ N : Subgroup G) : Set G) :=
      le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp inf_le_right)
        (le_centralizer_iff.mp (inf_le_left.trans hNV)))
    have h2 : V ⊓ centralizer (d.nineResidual : Set G) ≤
        centralizer ((d.nineResidual ⊔ N : Subgroup G) : Set G) :=
      le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp inf_le_right)
        (le_centralizer_iff.mp (inf_le_left.trans hNV)))
    exact le_antisymm (le_inf inf_le_left
      (h1.trans (centralizer_le ((show d.nineResidual ≤ d.nineResidual ⊔ N from le_sup_left).trans hs.ge))))
      (le_inf inf_le_left (h2.trans (centralizer_le ((show B ≤ B ⊔ N from le_sup_left).trans hs.le))))
  have hcore : B.pCoreIn 2 ≤ centralizer (V : Set G) := by
    have htwo : IsPGroup 2 ((pCore 2 B).map f) := pCore_isPGroup.map f
    have hthree : IsPGroup 3 ((pCore 2 B).map f) :=
      (IsPGroup.of_card (p := 3) (n := 1) (hcard.trans (pow_one 3).symm)).of_injective
        (inclusion ((map_le_range f (pCore 2 B)).trans hr.le)) (inclusion_injective _)
    have hz : (pCore 2 B).map f = ⊥ := by
      have hd := htwo.disjoint_of_coprime hthree (by decide : Nat.Coprime 2 3)
      exact disjoint_self.mp hd
    have hk := (Subgroup.map_eq_bot_iff (pCore 2 B) (f := f)).mp hz
    rintro b ⟨x,hx,rfl⟩
    exact ((QuotientGroup.eq_one_iff _).mp (hk hx)).2
  let := h.elementary
  refine ⟨hmove,?_,hcore,hi,hfix⟩
  rw [←hmove]
  exact commutator_isPPerfect_idempotent B V hB (IsElementaryAbelian.isPGroup 2 V) hnB

/-- The source residual Y₀ moves the entire original plane and its two-core
fixes that plane; no rank-two assumption on L₃(2) is used. -/
theorem ExchangedSource.linearThree_residual_action
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    {h : PreparedChosenModule T M V} (sp : d.PreExclusionSource h.normalized 3)
    (hTM : (T : Subgroup G) ≤ M) (a : d.ConstrainedL3Alternative) :
    ⁅V,d.linearThreeY⁆ = d.nineMovingPlane ∧
      ⁅d.nineMovingPlane,d.linearThreeY⁆ = d.nineMovingPlane ∧
      d.linearThreeY.pCoreIn 2 ≤ centralizer (V : Set G) ∧
      (¬ d.linearThreeY ≤ d.MZ) ∧
      (centralizer (V : Set G)).relIndex d.linearThreeY = 3 ∧
      V ⊓ centralizer (d.linearThreeY : Set G) = d.nineFixedPlane := by
  have hYC : d.linearThreeY ≤ M ⊓ d.G1 := (map_subtype_le _).trans
    (inf_le_inf_left M d.L_component.1)
  have hp : IsPPerfect 2 d.linearThreeY := isPPerfect_embedded_pResidual 2 _
  have hne : ¬ d.linearThreeY ≤ centralizer (V : Set G) := by
    intro hc
    exact s.linearThreeY_not_centralizes hTM h a
      ((show d.nineMovingPlane ≤ V from le_normalizer_iff_commutator_le_left.mp
        (((map_subtype_le _).trans inf_le_left).trans h.normalized)).trans
          (le_centralizer_iff.mp hc))
  obtain ⟨h1,h2,h3,hi,hfix⟩ := sp.moving_of_noncentral_twoPerfect (h := h) hYC hp hne
  exact ⟨h1,h2,h3,(fun he => hne (sp.twoPerfect_intersection_centralizes (h := h) hp
    (hYC.trans inf_le_left) he)),hi,hfix⟩

/-- The original moving plane is contained in the center of the actual
second-parabolic two-core, before any block-module identification. -/
theorem ExchangedSource.linearThree_moving_in_core_center
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    {h : PreparedChosenModule T M V} (sp : d.PreExclusionSource h.normalized 3)
    (hTM : (T : Subgroup G) ≤ M) (a : d.ConstrainedL3Alternative) :
    d.nineMovingPlane ≤ d.linearThreeY.pCoreIn 2 ⊓
      centralizer (d.linearThreeY.pCoreIn 2 : Set G) := by
  obtain ⟨hm,hm2,hcore,_⟩ := s.linearThree_residual_action (h := h) sp hTM a
  have hVnL : V ≤ normalizer (d.L : Set G) := by
    exact s.planes_sup.ge.trans (sup_le
      ((a.fixedPlane_centralizes hTM h).trans (Subgroup.centralizer_le_normalizer _))
      (le_sup_right.trans sp.residual_normalizes))
  have hVnP : V ≤ normalizer ((M ⊓ d.L : Subgroup G) : Set G) :=
    le_normalizer_inf (h.le_selected.trans M.le_normalizer) hVnL
  have hVnY : V ≤ normalizer (d.linearThreeY : Set G) :=
    hVnP.trans (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _))
  have hV2Y : d.nineMovingPlane ≤ d.linearThreeY :=
    hm ▸ le_normalizer_iff_commutator_le_right.mp hVnY
  have hV2V : d.nineMovingPlane ≤ V := by
    exact le_sup_right.trans s.planes_sup.le
  let := h.elementary
  exact le_inf (le_pCoreIn_of_normalizes
    ((IsElementaryAbelian.isPGroup 2 V).to_le hV2V) hV2Y
    (le_normalizer_iff_commutator_le_left.mpr hm2.le))
    (hV2V.trans (le_centralizer_iff.mp hcore))

/-- The exchanged second-parabolic residual fixes the moving plane and
moves the entire fixed plane. These are statements about the literal
conjugation map, not an abstract cubic actor. -/
theorem ExchangedSource.linearThree_exchanged_action
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    {h : PreparedChosenModule T M V} (sp : d.PreExclusionSource h.normalized 3)
    (hTM : (T : Subgroup G) ≤ M) (a : d.ConstrainedL3Alternative)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    IsPPerfect 2 (d.linearThreeY.map (MulAut.conj t).toMonoidHom) ∧
      d.linearThreeY.map (MulAut.conj t).toMonoidHom ≤
        centralizer (d.nineMovingPlane : Set G) ∧
      ⁅d.nineFixedPlane,d.linearThreeY.map (MulAut.conj t).toMonoidHom⁆ =
        d.nineFixedPlane := by
  have hm := (s.linearThree_residual_action (h := h) sp hTM a).2.1
  have he := s.exchanges t ht htS
  have hmove := congrArg (map (MulAut.conj t).toMonoidHom) hm
  rw [map_commutator,he.2] at hmove
  refine ⟨(isPPerfect_embedded_pResidual 2 (M ⊓ d.L)).of_surjective
    ((MulAut.conj t).toMonoidHom.subgroupMap d.linearThreeY)
    ((MulAut.conj t).toMonoidHom.subgroupMap_surjective d.linearThreeY),?_,hmove⟩
  have hc := congrArg (map (MulAut.conj t).toMonoidHom)
    (commutator_eq_bot_iff_le_centralizer.mpr d.fixedPlane_centralizes_linearThreeY)
  rw [map_commutator,Subgroup.map_bot,he.1,commutator_comm] at hc
  exact commutator_eq_bot_iff_le_centralizer.mp hc

/-- Original 1.2.1(3) applies in the full normalizer of V₁, where L
remains a C-component. Thus the literal exchanged two-residual acts on L. -/
theorem ExchangedSource.linearThree_exchanged_normalizes
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    {h : PreparedChosenModule T M V} (sp : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M) (a : d.ConstrainedL3Alternative)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    d.linearThreeY.map (MulAut.conj t).toMonoidHom ≤ normalizer (d.L : Set G) := by
  let A := d.linearThreeY.map (MulAut.conj t).toMonoidHom
  let N := normalizer (d.nineFixedPlane : Set G)
  obtain ⟨hp,_,hm⟩ := s.linearThree_exchanged_action (h := h) sp hTM a ht htS
  have hAN : A ≤ N := le_normalizer_iff_commutator_le_left.mpr hm.le
  have hLC := le_centralizer_iff.mp (a.fixedPlane_centralizes hTM h)
  have hLN : d.L ≤ N := hLC.trans (Subgroup.centralizer_le_normalizer _)
  have hL : (d.L.subgroupOf N).IsCComponent :=
    d.L_isCComponent_in_G1.in_normalizer_of_centralizes hLC
      (centralizer_le s.marked_le_fixed)
  have hne : d.nineFixedPlane ≠ ⊥ := by
    intro he
    rcases s.sizes with hs | hs <;> have hc := hs.2.2.1 <;> rw [he,card_bot] at hc <;> omega
  let := h.elementary
  have htwo : IsPGroup 2 d.nineFixedPlane :=
    (IsElementaryAbelian.isPGroup 2 V).to_le inf_le_left
  have hN := hG.twoLocal_sqtk ⟨d.nineFixedPlane,hne,htwo,rfl⟩
  have hquot : IsSQTK KnownSimple.IsKnownSimple (N ⧸ pCore 2 N) := by
    refine ⟨?_,hN.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 N) pCore_isPGroup).trans
      (hN.stronglyQuasithin p hp ho)
  have hAp : IsPPerfect 2 (A.subgroupOf N) := hp.of_surjective
    (subgroupOfEquivOfLe hAN).symm.toMonoidHom (subgroupOfEquivOfLe hAN).symm.surjective
  have hn := Chapter1.Section02.twoPerfect_normalizes_cComponent_source hquot hL hAp
  have hh := (map_mono (f := N.subtype) hn).trans
    ((d.L.subgroupOf N).le_normalizer_map N.subtype)
  rwa [map_subgroupOf_eq_of_le hAN,map_subgroupOf_eq_of_le hLN] at hh


/-- The action kernel on V₂ is the action kernel on V, and its index in
Y₀ is exactly three. The complementary plane is centralized by Y₀. -/
theorem ExchangedSource.linearThree_moving_action_kernel
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    {h : PreparedChosenModule T M V} (sp : d.PreExclusionSource h.normalized 3)
    (hTM : (T : Subgroup G) ≤ M) (a : d.ConstrainedL3Alternative) :
    d.linearThreeY ⊓ centralizer (d.nineMovingPlane : Set G) =
      d.linearThreeY ⊓ centralizer (V : Set G) ∧
    (centralizer (d.nineMovingPlane : Set G)).relIndex d.linearThreeY = 3 ∧
    d.nineMovingPlane ⊓ centralizer (d.linearThreeY : Set G) = ⊥ := by
  obtain ⟨_,_,_,_,hi,hfix⟩ := s.linearThree_residual_action (h := h) sp hTM a
  have hV2 : d.nineMovingPlane ≤ V := le_sup_right.trans s.planes_sup.le
  have he : d.linearThreeY ⊓ centralizer (d.nineMovingPlane : Set G) =
      d.linearThreeY ⊓ centralizer (V : Set G) := by
    refine le_antisymm (le_inf inf_le_left ?_) (inf_le_inf_left _ (centralizer_le hV2))
    apply le_centralizer_iff.mp
    apply s.planes_sup.ge.trans
    exact sup_le (d.fixedPlane_centralizes_linearThreeY.trans (centralizer_le inf_le_left))
      (le_centralizer_iff.mp inf_le_right)
  refine ⟨he,?_,?_⟩
  · rw [←inf_relIndex_left d.linearThreeY (centralizer (d.nineMovingPlane : Set G)),he,
      inf_relIndex_left]
    exact hi
  · apply le_bot_iff.mp
    have hf : d.nineMovingPlane ⊓ centralizer (d.linearThreeY : Set G) ≤ d.nineFixedPlane :=
      (inf_le_inf_right _ hV2).trans hfix.le
    exact (le_inf hf inf_le_left).trans s.planes_inf.le


/-- A precise reduction for the remaining block calculation. If the moving
plane has trivial image modulo O₂(L), its movement puts it inside U(L).
Otherwise the literal quotient contains an involution fixed by the exchanged
residual. No containment of the whole center of O₂(Y₀) in U(L) is assumed. -/
theorem ExchangedSource.linearThree_layer_or_quotient_involution
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    {h : PreparedChosenModule T M V} (sp : d.PreExclusionSource h.normalized 3)
    (hTM : (T : Subgroup G) ≤ M) (a : d.ConstrainedL3Alternative) :
    d.nineMovingPlane ≤ d.linearThreeU ∨
      ∃ v : d.L, (v : G) ∈ d.nineMovingPlane ∧
        orderOf (QuotientGroup.mk' (pCore 2 d.L) v) = 2 := by
  have hYL : d.linearThreeY ≤ d.L := (map_subtype_le _).trans inf_le_right
  have hV2L : d.nineMovingPlane ≤ d.L :=
    ((s.linearThree_moving_in_core_center (h := h) sp hTM a).trans inf_le_left).trans
      ((pCoreIn_le 2 _).trans hYL)
  by_cases hc : d.nineMovingPlane ≤ d.L.pCoreIn 2
  · left
    have hm := (s.linearThree_residual_action (h := h) sp hTM a).2.1
    have hU : ⁅d.L.pCoreIn 2,d.L⁆ = d.linearThreeU := by
      change ⁅(pCore 2 d.L).map d.L.subtype,d.L⁆ =
        (⁅pCore 2 d.L,(⊤ : Subgroup d.L)⁆).map d.L.subtype
      rw [map_commutator,←MonoidHom.range_eq_map,range_subtype]
    exact hm.ge.trans ((commutator_mono hc hYL).trans hU.le)
  · right
    obtain ⟨v,hv,hvc⟩ := Set.not_subset.mp hc
    let w : d.L := ⟨v,hV2L hv⟩
    refine ⟨w,hv,orderOf_eq_prime ?_ ?_⟩
    · let := h.elementary
      have hvV : v ∈ V := (le_sup_right.trans s.planes_sup.le) hv
      have hw : w ^ 2 = 1 := Subtype.ext
        (elemPow_eq_one_of_isElementaryAbelian v hvV)
      rw [←map_pow,hw,map_one]
    · intro he
      exact hvc (mem_map.mpr ⟨w,(QuotientGroup.eq_one_iff _).mp he,rfl⟩)


/-- If the moving plane lies in the block layer, it embeds into the actual
natural module quotient: its intersection with the central attachment is
trivial. The module of order eight then excludes the sixteen-element row. -/
theorem ExchangedSource.linearThree_row_four_of_layer
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    {h : PreparedChosenModule T M V} (sp : d.PreExclusionSource h.normalized 3)
    (hTM : (T : Subgroup G) ≤ M) (a : d.ConstrainedL3Alternative)
    (hVU : d.nineMovingPlane ≤ d.linearThreeU) :
    d.row = .four ∧ Nat.card d.Z1 = 2 ∧ Nat.card d.nineFixedPlane = 4 ∧
      Nat.card d.nineMovingPlane = 4 := by
  have hVL : d.nineMovingPlane ≤ d.L := hVU.trans (map_subtype_le _)
  have hEu : d.nineMovingPlane.subgroupOf d.L ≤ blockU d.L := by
    intro x hx
    obtain ⟨u,hu,he⟩ := hVU hx
    exact (Subtype.ext he : u = x) ▸ hu
  let i : d.nineMovingPlane →* blockU d.L := (inclusion hEu).comp
    (subgroupOfEquivOfLe hVL).symm.toMonoidHom
  let f := (QuotientGroup.mk' (blockFixed d.L)).comp i
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro x hx
    have hz0 : i x ∈ blockFixed d.L := (QuotientGroup.eq_one_iff _).mp hx
    have hz : (i x : d.L) ∈ center d.L := hz0
    have hc : (x : G) ∈ centralizer (d.linearThreeY : Set G) := by
      intro y hy
      have hyL : y ∈ d.L := ((map_subtype_le _).trans inf_le_right) hy
      exact congrArg (fun z : d.L => (z : G)) (mem_center_iff.mp hz ⟨y,hyL⟩)
    have he := (s.linearThree_moving_action_kernel (h := h) sp hTM a).2.2.le
      ⟨x.property,hc⟩
    exact Subtype.ext he
  have hb := Nat.card_le_card_of_injective f hf
  have hm : Nat.card (BlockModule d.L) = 8 := by
    simpa using a.block.module_card
  change Nat.card d.nineMovingPlane ≤ Nat.card (BlockModule d.L) at hb
  rw [hm] at hb
  rcases s.sizes with hs | hs
  · exact hs
  · have hc := hs.2.2.2
    omega

/-- The remaining model calculation has two literal branches. In the core
branch the plane is an order-four subgroup of U(L); in the other branch it
contains an element whose image in L/O₂(L) is an involution. -/
theorem ExchangedSource.linearThree_moving_dichotomy
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    {h : PreparedChosenModule T M V} (sp : d.PreExclusionSource h.normalized 3)
    (hTM : (T : Subgroup G) ≤ M) (a : d.ConstrainedL3Alternative) :
    (d.nineMovingPlane ≤ d.linearThreeU ∧ d.row = .four ∧
      Nat.card d.Z1 = 2 ∧ Nat.card d.nineFixedPlane = 4 ∧
      Nat.card d.nineMovingPlane = 4) ∨
    (∃ v : d.L, (v : G) ∈ d.nineMovingPlane ∧
      orderOf (QuotientGroup.mk' (pCore 2 d.L) v) = 2) := by
  rcases s.linearThree_layer_or_quotient_involution (h := h) sp hTM a with hU | hv
  · exact Or.inl ⟨hU,s.linearThree_row_four_of_layer (h := h) sp hTM a hU⟩
  · exact Or.inr hv


/-- In the noncore branch, fixation of the quotient involution forces the
exchanged residual to centralize L/O₂(L). This uses the actual quotient
isomorphism from the parabolic marking. -/
theorem ExchangedSource.linearThree_exchanged_core_quotient_of_involution
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    {h : PreparedChosenModule T M V} (sp : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M) (a : d.ConstrainedL3Alternative)
    (v : d.L) (hv : (v : G) ∈ d.nineMovingPlane)
    (hv2 : orderOf (QuotientGroup.mk' (pCore 2 d.L) v) = 2)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    ⁅d.linearThreeY.map (MulAut.conj t).toMonoidHom,d.L⁆ ≤ d.L.pCoreIn 2 := by
  let A := d.linearThreeY.map (MulAut.conj t).toMonoidHom
  have hn : A ≤ normalizer (d.L : Set G) :=
    s.linearThree_exchanged_normalizes (h := h) sp hG hTM a ht htS
  obtain ⟨hp,hc,_⟩ := s.linearThree_exchanged_action (h := h) sp hTM a ht htS
  obtain ⟨e,_⟩ := a.marked_parabolic
  let b : A →* MulAut d.L := d.L.normalizerMonoidHom.comp (inclusion hn)
  let f : A →* MulAut Matrix.PSL3Two.SL :=
    ((MulAut.congr e).toMonoidHom.comp (quotientAut (pCore 2 d.L))).comp b
  let q := QuotientGroup.mk' (pCore 2 d.L)
  have hfix (y : A) : f y (e (q v)) = e (q v) := by
    change e (quotientAut (pCore 2 d.L) (b y) (e.symm (e (q v)))) = e (q v)
    rw [e.symm_apply_apply,quotientAut_apply_mk]
    have hb : b y v = v := by
      apply Subtype.ext
      change (y : G) * (v : G) * (y : G)⁻¹ = v
      have hh := hc y.property v hv
      rw [←hh,mul_inv_cancel_right]
    rw [hb]
  have hf : f = 1 := Matrix.PSL3Two.InvolutionResidual.action_eq_one_of_fixed_involution
    hp f (e (q v)) ((e.orderOf_eq (q v)).trans hv2) hfix
  apply commutator_le.mpr
  intro y hy l hl
  let yA : A := ⟨y,hy⟩
  let lL : d.L := ⟨l,hl⟩
  have hh := congrArg (fun k : A →* MulAut Matrix.PSL3Two.SL => k yA (e (q lL))) hf
  change e (quotientAut (pCore 2 d.L) (b yA) (e.symm (e (q lL)))) = e (q lL) at hh
  rw [e.symm_apply_apply,quotientAut_apply_mk] at hh
  have hk : b yA lL * lL⁻¹ ∈ pCore 2 d.L := by
    simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp (e.injective hh)
  exact mem_map.mpr ⟨b yA lL * lL⁻¹,hk,rfl⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData





