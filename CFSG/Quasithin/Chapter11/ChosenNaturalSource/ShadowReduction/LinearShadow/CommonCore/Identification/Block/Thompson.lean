module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Block.Complement.Recovery
public import Theory.GroupTheory.ElementaryThompsonFixedIndex
public import Theory.GroupTheory.ElementaryThompsonElementaryCore
public import Theory.GroupTheory.ElementaryThompsonRelative

/-!
# The Thompson subgroup of the original pair extension

The shear action shows that a vector outside V₂ has centralizer in P
contained in V₂. A maximum elementary subgroup of PV escaping P would
therefore have fixed index at least q² and at most |PV:P|=q, a contradiction.
Thus J(PV)=P. The literal identity R₂∩L=PV then makes both L₂ and the
original inner Sylow normalizer preserve P. The counterexample application
constructs all these inputs, including the full plane-radical image.

Source: Aschbacher--Smith, refs/quasithin.pdf, printed p.774,
the final sentence of the third paragraph. The earlier source inputs are
discharged by qt-d-1222-shadow-common-core and its existing producers.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Matrix
open scoped IsMulCommutative commutatorElement MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
namespace OriginalBlock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G} {h : G}
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

/-- A nonplane vector detects every nonidentity shear. -/
theorem radical_centralizer_outside_plane
    (hcent : L ⊓ centralizer (V : Set G) = V)
    (v : V) (hv : (v : G) ∉ (SL3.flag D S a).Vi 1) :
    (SL3.flag D S a).Ri 1 ⊓ L ⊓ centralizer ({(v : G)} : Set G) ≤ V := by
  intro x hx
  let r : (SL3.flag D S a).Ri 1 := ⟨x,hx.1.1⟩
  let e := SL3.RadicalAction.vectorEquiv D S a
  have hv2 : (e v).toAdd 2 ≠ 0 := fun he =>
    hv ((SL3.RadicalAction.vectorEquiv_mem_plane D S a v).mpr he)
  have hcomm : SL3.RadicalAction.vectorCommutator D S a r v = 1 := by
    apply Subtype.ext
    rw [SL3.RadicalAction.vectorCommutator_coe]
    exact commutatorElement_eq_one_iff_commute.mpr
      (mem_centralizer_singleton_iff.mp hx.2)
  obtain ⟨b,c,hr⟩ := SL3.RadicalAction.radicalOperator_shear D S a r
  have he := SL3.RadicalAction.vectorCommutator_coordinates D S a r v
  rw [hcomm,map_one,hr] at he
  have hb : b = 0 := by
    have he0 := congrFun he 0
    have hz : b * (e v).toAdd 2 = 0 := by simpa [e] using he0.symm
    exact (mul_eq_zero.mp hz).resolve_right hv2
  have hc : c = 0 := by
    have he1 := congrFun he 1
    have hz : c * (e v).toAdd 2 = 0 := by simpa [e] using he1.symm
    exact (mul_eq_zero.mp hz).resolve_right hv2
  apply hcent.le
  refine ⟨hx.1.2,?_⟩
  intro w hw
  let w' : V := ⟨w,hw⟩
  have hh : SL3.RadicalAction.vectorCommutator D S a r w' = 1 := by
    apply e.injective
    apply Multiplicative.toAdd.injective
    rw [SL3.RadicalAction.vectorCommutator_coordinates,hr,hb,hc,map_one]
    ext i
    fin_cases i <;> simp
  have hmul := congrArg (fun y : V => (y : G)) hh
  change ⁅x,w⁆ = 1 at hmul
  exact (commutatorElement_eq_one_iff_commute.mp hmul).symm

omit [Finite G] in
private theorem card_inf_mul_index (A B : Subgroup G) :
    Nat.card (A ⊓ B : Subgroup G) * A.relIndex B = Nat.card B := by
  simpa only [relIndex_bot_left,inf_relIndex_right] using
    relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊓ B) B bot_le inf_le_right

/-- The common pair is the unique maximum elementary subgroup of PV. -/
theorem pairJoin_thompson
    (P B : Subgroup G) [IsElementaryAbelian 2 P]
    (hPL : P ≤ L) (hPR : P ≤ (SL3.flag D S a).Ri 1)
    (hcent : L ⊓ centralizer (V : Set G) = V)
    (hB : B = (SL3.flag D S a).Vi 1) (hPV : P ⊓ V = B)
    (hPcard : Nat.card P = (2 ^ S.field.degree)^4)
    (hBcard : Nat.card B = (2 ^ S.field.degree)^2)
    (hVcard : Nat.card V = (2 ^ S.field.degree)^3) :
    Stellmacher.elementaryAbelianMaxJ (P ⊔ V) = P := by
  let q := 2 ^ S.field.degree
  have hq : 1 < q := Nat.one_lt_pow (by have := S.nonbinary; omega) (by decide)
  have hnV : P ≤ normalizer (V : Set G) := hPL.trans D.normalizes
  have hmul := card_mul_eq_card_inf_mul_card_sup_of_normalizes V P hnV
  rw [inf_comm V P,hPV,sup_comm V P,hBcard,hPcard,hVcard] at hmul
  have hi := card_inf_mul_index P (P ⊔ V)
  rw [inf_eq_left.mpr le_sup_left,hPcard] at hi
  have hindex : P.relIndex (P ⊔ V) = q := by
    have hp : 0 < q := by omega
    change q^3 * q^4 = q^2 * Nat.card (P ⊔ V : Subgroup G) at hmul
    change q^4 * P.relIndex (P ⊔ V) = Nat.card (P ⊔ V : Subgroup G) at hi
    have hpow : q^3 * q^4 = q^2 * (q^4 * q) := by ring
    rw [←hi,hpow] at hmul
    exact (Nat.mul_left_cancel (pow_pos hp 4)
      (Nat.mul_left_cancel (pow_pos hp 2) hmul)).symm
  have hfixed (g : G) (hg : g ∈ P ⊔ V) (hgP : g ∉ P) :
      P ⊓ centralizer ({g} : Set G) ≤ B := by
    let : (V.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer D.normalizes
    have hgL : g ∈ L := sup_le hPL D.le_component hg
    have hmem : (⟨g,hgL⟩ : L) ∈ P.subgroupOf L ⊔ V.subgroupOf L := by
      rw [←subgroupOf_sup hPL D.le_component]
      exact hg
    obtain ⟨p,hp,v,hv,he⟩ := mem_sup_of_normal_right.mp hmem
    have hvB : (v : G) ∉ (SL3.flag D S a).Vi 1 := by
      intro hvB
      have hvP : (v : G) ∈ P := (hPV.symm.le (hB.symm ▸ hvB)).1
      have heG : (p : G) * (v : G) = g := congrArg (fun l : L => (l : G)) he
      exact hgP (heG ▸ P.mul_mem hp hvP)
    intro x hx
    have hxp : Commute x (p : G) :=
      (P.le_centralizer hx.1 p hp).symm
    have hxg : Commute x ((p : G) * (v : G)) := by
      rw [show (p : G) * (v : G) = g from congrArg (fun l : L => (l : G)) he]
      exact (mem_centralizer_singleton_iff.mp hx.2)
    have hxv : Commute x (v : G) := by
      apply mul_left_cancel (a := (p : G))
      calc
        (p : G) * (x * (v : G)) = x * ((p : G) * (v : G)) := by
          rw [←mul_assoc,←hxp.eq,mul_assoc]
        _ = ((p : G) * (v : G)) * x := hxg.eq
        _ = (p : G) * ((v : G) * x) := mul_assoc _ _ _
    have hxV := radical_centralizer_outside_plane D S a hcent (⟨v,hv⟩ : V) hvB
      ⟨⟨hPR hx.1,hPL hx.1⟩,mem_centralizer_singleton_iff.mpr hxv⟩
    exact hPV.le ⟨hx.1,hxV⟩
  apply Stellmacher.elementaryAbelianMaxJ_eq_of_elementary_overgroup _ _ ?_ le_sup_left inferInstance
  apply sSup_le
  intro A hA
  by_contra hnot
  obtain ⟨g,hg,hgP⟩ := SetLike.not_le_iff_exists.mp hnot
  have hcb : P ⊓ centralizer (A : Set G) ≤ B :=
    (inf_le_inf_left P (centralizer_le (by simpa using hg))).trans (hfixed g (hA.1 hg) hgP)
  have hsmall := (Stellmacher.maxElementary_fixedIndex_le_relIndex (P ⊔ V) P A P
    le_sup_left le_rfl P.le_centralizer hA)
  have hiA := (hsmall.1.trans hsmall.2).trans
    (relIndex_le_of_le_right hA.1 index_ne_zero_of_finite)
  rw [hindex] at hiA
  have hb := card_le_of_le hcb
  rw [hBcard] at hb
  have hh := card_inf_mul_index (centralizer (A : Set G)) P
  rw [inf_comm,hPcard] at hh
  have hbound : q^4 ≤ q^2 * q := by
    rw [←hh]
    exact Nat.mul_le_mul hb hiA
  have hstrict : q^2 * q < q^4 := by
    rw [←pow_succ]
    exact Nat.pow_lt_pow_right hq (by decide)
  exact (not_lt_of_ge hbound hstrict)

/-- Both the plane residual and the original Cartan normalizer preserve the pair. -/
theorem pair_normalizers
    (P : Subgroup G)
    (hR : (SL3.flag D S a).Ri 1 ⊓ L = P ⊔ V)
    (hJ : Stellmacher.elementaryAbelianMaxJ (P ⊔ V) = P) :
    (SL3.flag D S a).Li 1 ≤ normalizer (P : Set G) ∧
      cartanNormalizer T L ≤ normalizer (P : Set G) := by
  have hfun (N : Subgroup G)
      (hn : N ≤ normalizer (((SL3.flag D S a).Ri 1 ⊓ L : Subgroup G) : Set G)) :
      N ≤ normalizer (P : Set G) := by
    rw [hR] at hn
    exact (hn.trans (Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ _)).trans_eq
      (congrArg (fun Q : Subgroup G => normalizer (Q : Set G)) hJ)
  constructor
  · apply hfun
    apply (le_inf ?_ ?_).trans inf_normalizer_le_normalizer_inf
    · exact (le_sup_left : (SL3.flag D S a).Li 1 ≤
        (SL3.flag D S a).Li 1 ⊔ (T : Subgroup G)).trans
        (((SL3.flag D S a).Li 1 ⊔ (T : Subgroup G)).le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
    · exact ((localResidual_le _).trans inf_le_left).trans L.le_normalizer
  · apply hfun
    have he : (SL3.flag D S a).Ri 1 ⊓ L =
        ((T : Subgroup G) ⊓ L) ⊓ centralizer ((SL3.flag D S a).Vi 1 : Set G) := by
      rw [←SL3.RadicalAction.sylow_centralizer_plane D S a]
      exact inf_right_comm _ _ _
    rw [he]
    have hn := (SL3.flag D S a).normalizer_le_flag_normalizer
      (SL3.flag_inner_unique D S a) 1
    have hnc : normalizer ((SL3.flag D S a).Vi 1 : Set G) ≤
        normalizer (centralizer ((SL3.flag D S a).Vi 1 : Set G) : Set G) :=
      (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp inferInstance
    exact (le_inf cartanNormalizer_normalizes_intersection (hn.trans hnc)).trans
      inf_normalizer_le_normalizer_inf

end OriginalBlock

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {h : G}

theorem source_pair_thompson_and_normalizers
    (cL : Coordinates D S.field) (flag : InvariantFlag cL)
    (s : Hypothesis1131At D S U₁ H) (p : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H) (hh : h ∈ H)
    (hm : h ∉ normalizer (L : Set G))
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hnot : ¬ V ≤ H.pCoreIn 2)
    (hmodel : ClassicalGroup.IsPSL
      (outsideResidual H ⧸ pCore 2 (outsideResidual H)) 2 (2 ^ S.field.degree))
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (R : Sylow 2 (residualStar T H))
    (hR : (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      (V.subgroupOf H).map (starProjection T H))
    (cK : NaturalQuotientMarking T H S.field)
    (A X : Subgroup G) (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hX : IsCartan T L X) (hAX : oddCartanPart A ≤ X) :
    L.pCoreIn 2 = V ∧ L ⊓ centralizer (V : Set G) = V ∧
      ∃ a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3),
        axis V H = (SL3.flag D S a).Vi 1 ∧
        pairCore V H h ⊓ V = (SL3.flag D S a).Vi 1 ∧
        Nat.card (pairCore V H h) = (2 ^ S.field.degree)^4 ∧
        (SL3.flag D S a).Ri 1 ⊓ L = pairCore V H h ⊔ V ∧
        Stellmacher.elementaryAbelianMaxJ (pairCore V H h ⊔ V) = pairCore V H h ∧
        ((pairCore V H h).subgroupOf L).map (SL3.PlaneAction.alignedQuotient D S a) =
          (Matrix.PSL3.LinearThree.lineRadicalSL S.field.Carrier).map
            (Matrix.PSL3.LinearThree.lineLocalSL S.field.Carrier).subtype ∧
        (SL3.flag D S a).Li 1 ≤ normalizer (pairCore V H h : Set G) ∧
        cartanNormalizer T L ≤ normalizer (pairCore V H h : Set G) := by
  obtain ⟨a,hPL,hB,hPV,hcard,hT,hcomp,cover,hcover⟩ :=
    source_pair_invariant_complement cL flag s p hc hh hm hfixed hf hnot hmodel hG2
      R hR cK A X hA hHall hX hAX
  obtain ⟨hd,hgen,hE,hCcard,him,hfull,hRnorm⟩ := hcomp
  obtain ⟨hgenL,hLT,hL⟩ := source_pair_core_centralization a (SL3.flag D S a)
    (SL3.flag_inner_unique D S a) s p hc hh hm hfixed hf hnot hmodel R hR cK
      A X hA hHall hX hAX
  have hcore : L.pCoreIn 2 = V ∧ L ⊓ centralizer (V : Set G) = V := by
    rcases OriginalBlock.core_alternative D S a hL with hcore | ⟨h4,hbad⟩
    · exact hcore
    · exact (hbad (OriginalBlock.seedQuotient_core_eq_bot_of_complement D S a hL h4
        hd hE him hT)).elim
  have hk := source_residual_le_pairGroup s hh hm hnot hmodel R hR
  have hz := pair_intersection_eq_bot s hf hk
  let := pairCore_elementary s hh hz
  have hplaneCard : Nat.card (axis V H) = ((2 ^ S.field.degree)^2) := by
    apply Nat.pow_left_injective (by decide : 2 ≠ 0)
    simpa only [←pow_mul,Nat.mul_assoc] using (pairCore_card s hh hz).symm.trans hcard
  have hrad := OriginalBlock.plane_radical_inter_component_eq_pairJoin D S a hcore.1 hPL hgen
  have hVcard : Nat.card V = (2 ^ S.field.degree)^3 := by
    calc
      Nat.card V = Nat.card (Fin 3 → S.field.Carrier) :=
        Nat.card_congr ((SL3.naturalEquiv D S a).toEquiv.trans Multiplicative.toAdd)
      _ = _ := by rw [Nat.card_fun,Nat.card_fin,S.field.card_eq]
  have hJ := OriginalBlock.pairJoin_thompson D S a (pairCore V H h) (axis V H)
    hPL (pairCore_le_plane_radical a (SL3.flag D S a) s hh hz hB) hcore.2 hB
    (pairCore_inf_seed hh) hcard hplaneCard hVcard
  have himage : ((pairCore V H h).subgroupOf L).map (SL3.PlaneAction.alignedQuotient D S a) =
      (Matrix.PSL3.LinearThree.lineRadicalSL S.field.Carrier).map
        (Matrix.PSL3.LinearThree.lineLocalSL S.field.Carrier).subtype := by
    change (((pairCore V H h).subgroupOf L).map (OriginalBlock.seedProjection D)).map
      (OriginalBlock.alignedSeedModel D S a) = _ at him
    rw [Subgroup.map_map] at him
    exact him
  exact ⟨hcore.1,hcore.2,a,hB,hPV,hcard,hrad,hJ,himage,
    OriginalBlock.pair_normalizers D S a (pairCore V H h) hrad hJ⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
