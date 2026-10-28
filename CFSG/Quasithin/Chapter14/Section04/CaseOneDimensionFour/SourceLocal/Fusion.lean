module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.SourceLocal.ActionAlternative
public import CFSG.Quasithin.Chapter14.Section04.DimensionFour.NonsplitGeometry
public import Theory.GroupTheory.AutomorphismLocalDisplacement
public import Theory.Representation.SLThreeCentralExtension.GroupFixedSpace

/-!
# Completing the c₂ fusion branch in the original order-32 setup

The c₂ action gives C_G(L)=1. Every element of C_G(V) fixes V pointwise,
so its square fixes L; hence A=C_G(V) is elementary. The actual full action
of L on V gives M=LA. If H/O₂(H) has order 36, the source Sylow orders force
|A|=16 and L∩A=V. Both normality statements are relative to M=N_G(L).
Original uniqueness supplies N_G(A)≤M.

Conjugation on A has no fixed point under L. The binary four-space theorem
therefore puts each quotient-involution fixed space in L. The original
quaternion subgroup gives the literal quotient involution lifts and commuting
order-four witnesses. Together with the proved rank-three Sylow intersection,
these discharge every premise of the elementary-extension Thompson transfer
argument. Simplicity excludes the resulting index-two normal subgroup.

Consequently the c₂ branch constructs SourceLocalData and its genuine I.4.5
configuration without a fusion, quotient-order or generation callback. The
unconditional source consumer now leaves only the swapping branch, still
owned by qt-d-14414-g2-source. Universal I.4.5 remains qt-i45-g2-recognition;
EarlierSetupResults retains the original earlier-source producers, and final
14.4.14 assembly remains qt-d-14414-source.

Source: Aschbacher–Smith, 14.4.4(6) and 14.4.5, printed pp.1007–1008.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- In the c₂ branch the actual ambient seed centralizer is elementary.
A pointwise fixer of V squares to the identity on L, and C_G(L)=1. -/
theorem source_seed_centralizer_elementary_of_c2 (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (q : QuaternionCentralProductData F.U)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U)
    (hc2 : q.IsC2 (F.uAction s)) : IsElementaryAbelian 2 (centralizer (V : Set G)) := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  have hV := (source_block_core d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard).1
  have hVL : V ≤ L := hV.le.trans (L.pCoreIn_le 2)
  let E := V.subgroupOf L
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hVL
  have hVN : E = pCore 2 L := by
    change V.subgroupOf L = pCore 2 L
    rw [hV]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  let : E.Normal := by rw [hVN]; infer_instance
  have hself : centralizer (E : Set L) ≤ E := by
    intro x hx
    have hc : (x : G) ∈ centralizer (V : Set G) := by
      intro v hv
      exact congrArg Subtype.val (hx (⟨v,hVL hv⟩ : L) hv)
    have hh := H.centralizer_L.le ⟨x.property,hc⟩
    exact hV.ge hh
  have hp (x : centralizer (V : Set G)) : x ^ 2 = 1 := by
    let a : MulAut L := L.normalizerMonoidHom
      ⟨x, H.seed_centralizer_le previous.structural previous.uniqueness x.property⟩
    have hfix (v : L) (hv : v ∈ E) : a v = v := by
      apply Subtype.ext
      change (x : G) * (v : G) * (x : G)⁻¹ = v
      rw [← x.property v hv, mul_inv_cancel_right]
    have hsq (l : L) : (a ^ 2) l = l :=
      MulAut.square_apply_eq_on_normalizer E hself a hfix
        (by rw [E.normalizer_eq_top]; exact mem_top l)
    have hxC : (x : G) ^ 2 ∈ centralizer (L : Set G) := by
      intro l hl
      have hh := congrArg Subtype.val (hsq ⟨l,hl⟩)
      change (x : G) * ((x : G) * l * (x : G)⁻¹) * (x : G)⁻¹ = l at hh
      have he : (x : G) ^ 2 * l * ((x : G) ^ 2)⁻¹ = l := by
        simpa only [pow_two, mul_inv_rev, mul_assoc] using hh
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    rw [source_c2_block_centralizer d earlier hq chosen previous F hne hZ hcard
      g hgP hgH q s hsX hs hout hc2] at hxC
    exact Subtype.ext hxC
  exact {
    is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hp x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp }

/-- The ambient normalizer is the product of L and the full seed centralizer. -/
theorem source_normalizer_eq_seed_centralizer_join (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    normalizer (L : Set G) = L ⊔ centralizer (V : Set G) := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  have hMV := source_normalizer_le_seed_normalizer d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard
  apply le_antisymm _ (sup_le L.le_normalizer
    (H.seed_centralizer_le previous.structural previous.uniqueness))
  intro m hm
  obtain ⟨l,hl,he⟩ := H.full_L_action (V.normalizerMonoidHom ⟨m,hMV hm⟩)
  have hc : l⁻¹ * m ∈ centralizer (V : Set G) := by
    intro v hv
    have hv' := he (⟨v,hv⟩ : V)
    change l * v * l⁻¹ = m * v * m⁻¹ at hv'
    calc
      v * (l⁻¹ * m) = l⁻¹ * (l * v * l⁻¹) * m := by group
      _ = l⁻¹ * (m * v * m⁻¹) * m := by rw [hv']
      _ = (l⁻¹ * m) * v := by group
  have hx := (L ⊔ centralizer (V : Set G)).mul_mem (mem_sup_left hl) (mem_sup_right hc)
  simpa only [mul_inv_cancel_left] using hx

/-- The order-36 c₂ alternative gives precisely the source elementary sixteen,
with normality relative to M=N_G(L), and the normalizer control used by transfer. -/
theorem source_elementary_extension_of_c2_and_card_thirty_six (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (q : QuaternionCentralProductData F.U)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U)
    (hc2 : q.IsC2 (F.uAction s)) (h36 : Nat.card (HStar F.H) = 36) :
    let A := centralizer (V : Set G)
    let M := normalizer (L : Set G)
    IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧ A ≤ (T : Subgroup G) ∧
      L ⊓ A = V ∧ M = L ⊔ A ∧ (A.subgroupOf M).Normal ∧
      normalizer (A : Set G) ≤ M := by
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  let A := centralizer (V : Set G)
  let M := normalizer (L : Set G)
  have hAT : A ≤ (T : Subgroup G) := source_seed_centralizer_le_sylow d earlier
    hq chosen previous F hne hZ hcard
  have hTM := H.sylow_normalizes previous.structural
  have hMN : M ≤ normalizer (A : Set G) :=
    (source_normalizer_le_seed_normalizer d earlier hq chosen previous.structural
      previous.alternatives F hne hZ hcard).trans (normalizer_le_normalizer_centralizer V)
  have hV := (source_block_core d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard).1
  have hinter : L ⊓ A = V := H.centralizer_L.trans hV.symm
  have hcover : M = L ⊔ A := source_normalizer_eq_seed_centralizer_join d earlier
    hq chosen previous F hne hZ hcard
  have hT := (source_sylow_index_two_of_c2_and_card_thirty_six d earlier hq chosen previous
    F hne hZ hcard g hgP hgH q s hsX hs hout hc2 h36).1
  have hVc : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  have hLc : Nat.card L = 1344 := by
    have hcore : Nat.card (pCore 2 L) = 8 := by
      rw [← card_map_of_injective L.subtype_injective]
      change Nat.card (L.pCoreIn 2) = 8
      rwa [←hV]
    have hquot : Nat.card (L ⧸ pCore 2 L) = 168 :=
      (Nat.card_congr (H.naturalMarking.quotientEquiv.trans
        (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 3)).symm).toEquiv).trans
          Matrix.PSL3Two.card_PSL
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 L), hcore, hquot]
  have hMc : Nat.card M = 2688 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes L (T : Subgroup G) hTM
    rw [hLc,hT,inf_comm,(source_sylow_index d earlier hq chosen previous.structural
      previous.alternatives F hne hZ hcard).1,
      ←source_normalizer_eq_join d earlier hq chosen previous F hne hZ hcard] at hh
    change 1344 * 128 = 64 * Nat.card M at hh
    omega
  have hAc : Nat.card A = 16 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes L A
      (H.seed_centralizer_le previous.structural previous.uniqueness)
    rw [hLc,hinter,hVc,←hcover,hMc] at hh
    omega
  have hn : (A.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer (hAT.trans hTM)).mpr
    (hMN : M ≤ normalizer (A : Set G))
  have hNA : normalizer (A : Set G) ≤ M := by
    apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G)) _
      (T.isPGroup'.to_le hAT) (by intro he; rw [he,card_bot] at hAc; omega)
      ((source_normalizer_eq_join d earlier hq chosen previous F hne hZ hcard).symm.le.trans hMN)
    intro N hN hJN
    exact Set.mem_singleton_iff.mp ((H.maximal_unique previous.structural previous.uniqueness).2 ▸
      show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
        from ⟨hN,hJN⟩)
  exact ⟨source_seed_centralizer_elementary_of_c2 d earlier hq chosen previous F hne hZ hcard
    g hgP hgH q s hsX hs hout hc2,hAc,hAT,hinter,hcover,hn,hNA⟩
private theorem transfer_of_elementary_extension
    (T : Sylow 2 G) (M L A V U : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hLM : L ≤ M) (hAT : A ≤ (T : Subgroup G))
    [(L.subgroupOf M).Normal] [(A.subgroupOf M).Normal] [(V.subgroupOf L).Normal]
    [IsElementaryAbelian 2 A] (hcover : M = L ⊔ A)
    (hA : Nat.card A = 16) (hinter : L ⊓ A = V) (hV : Nat.card V = 8)
    (hUL : U ≤ L) (hVU : V ≤ U) (q : QuaternionCentralProductData U)
    (e : (L ⧸ V.subgroupOf L) ≃* Matrix.PSL3Two.PSL)
    (hrank : primeRank 2 ((T : Subgroup G) ⊓ L : Subgroup G) ≤ 3)
    (hCZ : centralizer (L : Set G) = ⊥)
    (hnorm : normalizer (A : Set G) ≤ normalizer (L : Set G))
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) : False := by
  let L₀ := L.subgroupOf M
  let A₀ := A.subgroupOf M
  let U₀ := (U.subgroupOf M).subgroupOf L₀
  have hAM : A ≤ M := hAT.trans hTM
  have hUM : U ≤ M := hUL.trans hLM
  have hVL : V ≤ L := hVU.trans hUL
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf hAM
  let el : L₀ ≃* L := subgroupOfEquivOfLe hLM
  have hmap : (A₀.subgroupOf L₀).map el.toMonoidHom = V.subgroupOf L := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hinter.le ⟨y.property,hy⟩
    · intro hx
      refine ⟨⟨⟨x,hLM x.property⟩,x.property⟩,(hinter.ge hx).2,rfl⟩
  let e₀ : (L₀ ⧸ A₀.subgroupOf L₀) ≃* Matrix.PSL3Two.PSL :=
    (QuotientGroup.congr _ _ el hmap).trans e
  have hV₀ : Nat.card (A₀.subgroupOf L₀) = 8 := by
    rw [← card_map_of_injective (f := el.toMonoidHom) el.injective, hmap,
      Nat.card_congr (subgroupOfEquivOfLe hVL).toEquiv,hV]
  have hVU₀ : A₀.subgroupOf L₀ ≤ U₀ := by
    intro x hx
    exact hVU (hinter.le ⟨x.property,hx⟩)
  let eu : U₀ ≃* U := (subgroupOfEquivOfLe (show U.subgroupOf M ≤ L₀ from
    comap_mono hUL)).trans (subgroupOfEquivOfLe hUM)
  have hcover₀ : L₀ ⊔ A₀ = ⊤ := by
    apply map_injective M.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hLM,map_subgroupOf_eq_of_le hAM,
      ←MonoidHom.range_eq_map,range_subtype]
    exact hcover.symm
  obtain ⟨hlift,hfour⟩ := DimensionFour.NonsplitGeometry.involution_geometry_of_binary_quotient
    L₀ A₀ U₀ (q.map eu.symm) hcover₀ hVU₀ hV₀ e₀
  have hA₀ : Nat.card A₀ = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAM).toEquiv).trans hA
  have hfix₀ : A₀ ⊓ centralizer (L₀ : Set M) = ⊥ := by
    apply bot_unique
    intro x hx
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hCZ]
    intro l hl
    have hh := hx.2 (⟨l,hLM hl⟩ : M) hl
    exact congrArg Subtype.val hh
  have hfixed : ∀ y ∈ L₀, orderOf (QuotientGroup.mk' A₀ y) = 2 →
      ∀ a ∈ A₀, Commute y a → a ∈ L₀ := by
    intro y hy hq a ha hc
    exact BinaryLinearThree.NaturalExtension.fixed_involutions_le_block L₀ A₀ hA₀ hfix₀
      (e₀.trans Matrix.PSL3Two.equiv.symm) ⟨y,hy⟩ hq a ha hc
  have hfour' (y : L) (hy : orderOf y = 2) : ∃ r : L, Commute y r ∧ orderOf r = 4 := by
    obtain ⟨r,hc,hr⟩ := hfour (el.symm y) ((el.symm.orderOf_eq y).trans hy)
    refine ⟨el r,?_,(el.orderOf_eq r).trans hr⟩
    have hh := hc.map el.toMonoidHom
    change Commute (el (el.symm y)) (el r) at hh
    simpa only [el.apply_symm_apply] using hh
  exact DimensionFour.NonsplitGeometry.elementary_extension_transfer_of_fixed_spaces
    T M L A hTM hLM hAT hcover₀ hA (by rw [hinter,hV]) hfixed hlift hrank
    hfour' hnorm hno

/-- The order-thirty-six c₂ alternative contradicts Thompson transfer in the
original simple ambient group. All local extension and fixed-space premises
are constructed here. -/
theorem source_not_card_thirty_six_of_c2 (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (q : QuaternionCentralProductData F.U)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U)
    (hc2 : q.IsC2 (F.uAction s)) : Nat.card (HStar F.H) ≠ 36 := by
  intro h36
  let := chosen.elementary
  let H := higherRankHypothesis d earlier hq chosen
  obtain ⟨he,hA,hAT,hinter,hcover,hn,hNA⟩ :=
    source_elementary_extension_of_c2_and_card_thirty_six d earlier hq chosen previous
      F hne hZ hcard g hgP hgH q s hsX hs hout hc2 h36
  let A := centralizer (V : Set G)
  let M := normalizer (L : Set G)
  let : IsElementaryAbelian 2 A := he
  let : (A.subgroupOf M).Normal := hn
  let : (L.subgroupOf M).Normal := normal_in_normalizer
  have hV := (source_block_core d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard).1
  have hVN : V.subgroupOf L = pCore 2 L := by
    rw [hV]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  let : (V.subgroupOf L).Normal := by rw [hVN]; infer_instance
  let e : (L ⧸ V.subgroupOf L) ≃* Matrix.PSL3Two.PSL :=
    (QuotientGroup.quotientMulEquivOfEq hVN).trans
      (H.naturalMarking.quotientEquiv.trans
        (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 3)).symm)
  have hno (N : Subgroup G) (hN : N.Normal) : N.index ≠ 2 := by
    let := d.qtke.simple
    rcases hN.eq_bot_or_eq_top with rfl | rfl
    · rw [index_bot]
      intro hh
      let : IsCyclic G := isCyclic_of_prime_card hh
      exact d.qtke.nonabelian inferInstance
    · simp
  exact transfer_of_elementary_extension T M L A V F.U
    (H.sylow_normalizes previous.structural) L.le_normalizer hAT hcover hA hinter
    (by simpa [F.last] using F.card 3 (by decide))
    (source_block_core d earlier hq chosen previous.structural previous.alternatives F hne hZ hcard).2
    (le_conjugateSpanBy V F.H) q e
    (source_sylow_rank_of_c2 d earlier hq chosen previous F hne hZ hcard
      g hgP hgH q s hsX hs hout hc2).le
    (source_c2_block_centralizer d earlier hq chosen previous F hne hZ hcard
      g hgP hgH q s hsX hs hout hc2) hNA hno

/-- The source c₂ action alone now constructs every field of SourceLocalData:
Thompson transfer discharges the previously retained order-eighteen premise. -/
theorem source_localData_of_c2 (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (q : QuaternionCentralProductData F.U)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U)
    (hc2 : q.IsC2 (F.uAction s)) : Nonempty (SourceLocalData L F) := by
  have h18 := (source_quotient_card_cases d earlier hq chosen previous F hne hZ hcard).resolve_right
    (source_not_card_thirty_six_of_c2 d earlier hq chosen previous F hne hZ hcard
      g hgP hgH q s hsX hs hout hc2)
  exact source_localData_of_c2_and_card_eighteen d earlier hq chosen previous F hne hZ hcard
    g hgP hgH q s hsX hs hout hc2 h18

/-- Apply the completed c₂ local constructor to the actual I.4.5 configuration. -/
theorem configuration_of_source_c2 (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (q : QuaternionCentralProductData F.U)
    (s : F.H) (hsX : (s : G) ∈ F.X g) (hs : s ^ 2 = 1) (hout : (s : G) ∉ F.U)
    (hc2 : q.IsC2 (F.uAction s)) : Nonempty (DimensionFour.G2ThreeConfiguration G) := by
  obtain ⟨localData⟩ := source_localData_of_c2 d earlier hq chosen previous F hne hZ hcard
    g hgP hgH q s hsX hs hout hc2
  exact configuration_of_source_local d earlier hq chosen previous.structural previous.alternatives
    F hne hZ hcard localData

/-- The unconditional source reduction now leaves only the swapping branch.
The ambient normalizer and fusion conclusions in the c₂ branch are proved. -/
theorem source_configuration_or_swapping (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (previous : EarlierSetupResults KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32) :
    Nonempty (DimensionFour.G2ThreeConfiguration G) ∨
      ∃ (q : QuaternionCentralProductData F.U) (g : G) (s : F.H),
        g ∈ L ∧ g ∈ F.P L ∧ g ∉ F.H ∧ (s : G) ∈ F.X g ∧ s ^ 2 = 1 ∧
        (s : G) ∉ F.U ∧ (T : Subgroup G) ⊓ L = F.U ⊔ zpowers (s : G) ∧
        (q.left.map F.U.subtype).map (MulAut.conj (s : G)).toMonoidHom =
          q.right.map F.U.subtype ∧
        ⁅F.U, zpowers (s : G)⁆ = F.U ⊓ centralizer ({(s : G)} : Set G) ∧
        IsElementaryAbelian 2 (zpowers (s : G) ⊔ ⁅F.U, zpowers (s : G)⁆ : Subgroup G) ∧
        Nat.card (zpowers (s : G) ⊔ ⁅F.U, zpowers (s : G)⁆ : Subgroup G) = 16 := by
  obtain ⟨q⟩ := source_quaternion d earlier hq chosen previous.structural
    previous.alternatives F hne hZ hcard
  obtain ⟨g,s,hgL,hgP,hgH,hsX,hs,hout,hTL⟩ := source_involution_sylow_exists
    d earlier hq chosen previous.structural previous.alternatives F hne hZ hcard
  rcases source_involution_action_dichotomy d earlier hq chosen previous F hne hZ hcard
    g hgP hgH q s hsX hs hout with hc2 | hswap
  · exact Or.inl (configuration_of_source_c2 d earlier hq chosen previous F hne hZ hcard
      g hgP hgH q s hsX hs hout hc2)
  · exact Or.inr ⟨q,g,s,hgL,hgP,hgH,hsX,hs,hout,hTL,hswap,
      q.elementary_sixteen_of_swap F.U s (congrArg Subtype.val hs) hout hswap⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
