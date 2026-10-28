module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48OrdinaryLocal
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.InnerRadicalNormalizer
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.JankoLargeCenterRadical.NativeQuotients
public import Theory.SpecificGroups.Janko4.PerfectCoverActions
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# The original doubled-binary ordinary component is not J₄

The actual radical intersection descends through the full component center
to a native J₄ radical. The whole six-space injects into its center. Inner
automorphism control of the perfect cover puts the full radical normalizer
in the original local subgroup, so it normalizes the original residual image.
That image has full two-core quotient SL₃(2), contrary to the native
large-center radical theorem. Neither local maximality nor residual
injectivity through the covering center is assumed.

Source: Aschbacher--Smith C.2.8, C.3.3--5 and C.4.8, pp.147,149--154;
the native large-center radical theorem uses An--O'Brien--Wilson (2003),
Section 4 and Table 1, with the completed native normalizer cover.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The whole original moved orbit gives the native radical's large center;
the original residual remains normal with its full binary-three quotient. -/
theorem sourceOrbit_binary_witness_ordinary_not_janko
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : IsComponent H K) :
    ¬ Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  rintro ⟨e⟩
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let R := (J.pCoreIn 2).comap j
  let W := D.sourceOrbit.comap j
  let B₀ := LH.comap j
  let P := R.map q
  let B := B₀.map q
  let N := normalizer (P : Set Janko4.Model)
  have hj : Function.Injective j := H.subtype_injective.comp K.subtype_injective
  have hjr : j.range = K.map H.subtype := by rw [MonoidHom.range_comp,range_subtype]
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hc := D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC
  have hLH : LH ≤ H := hc.component_le.trans hc.local_le
  have hLK := hc.ordinary_component_contains_original K hK
  have hLKg : LH ≤ K.map H.subtype := by
    intro l hl
    exact ⟨⟨l,hLH hl⟩,hLK hl,rfl⟩
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  have hspan : conjugateSpanBy LH (H ⊓ normalizer (L : Set G)) = LH :=
    le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy _ _)
  have hWL : D.sourceOrbit ≤ LH := hspan ▸ hc.module_le
  have hWmap : W.map j = D.sourceOrbit :=
    map_comap_eq_self ((hWL.trans hLKg).trans_eq hjr.symm)
  let bW : W ≃* D.sourceOrbit := (W.equivMapOfInjective j hj).trans
    (MulEquiv.subgroupCongr hWmap)
  have hWcard : Nat.card W = 64 := by
    rw [Nat.card_congr bW.toEquiv]
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.sourceOrbit)
    rw [Nat.card_congr Additive.toMul,Nat.card_zmod,
      D.sourceOrbit_binary_dimension h hd F hF hmodel] at hh
    exact hh
  have hWR : W ≤ R := comap_mono hWJ
  have hWC : W ≤ centralizer (R : Set K) := by
    intro w hw r hr
    obtain ⟨z,hz,he⟩ := hc.module_le_center_radical hw
    apply hj
    have hh := congrArg (J.pCoreIn 2).subtype (mem_center_iff.mp hz ⟨j r,hr⟩)
    change j r * (z : G) = (z : G) * j r at hh
    change (z : G) = j w at he
    simpa only [map_mul,he] using hh
  have hqi : Function.Injective (q.comp W.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro w hwk
    have hz : (w : K) ∈ center K := hk ▸ hwk
    have hcent : j w ∈ centralizer (LH : Set G) := by
      intro l hl
      let x : K := ⟨⟨l,hLH hl⟩,hLK hl⟩
      exact congrArg j (mem_center_iff.mp hz x)
    have he : j w = 1 := mem_bot.mp
      (D.sourceOrbit_binary_witness_fixed_eq_bot h hd F hF hmodel hw ▸
        (show j w ∈ D.sourceOrbit ⊓ centralizer (LH : Set G) from ⟨w.property,hcent⟩))
    exact Subtype.ext (hj (he.trans j.map_one.symm))
  let wP : W →* P := (q.comp W.subtype).codRestrict P
    (fun w => mem_map_of_mem q (hWR w.property))
  have hwPc (w : W) : wP w ∈ center P := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨r,hr,he⟩ := y.property
    apply Subtype.ext
    change (y : Janko4.Model) * q w = q w * y
    rw [←he]
    exact (q.map_mul r w).symm.trans ((congrArg q (hWC w.property r hr)).trans (q.map_mul w r))
  let wZ := wP.codRestrict (center P) hwPc
  have hwZ : Function.Injective wZ := by
    intro a b he
    exact hqi (congrArg (fun x : center P => ((x : P) : Janko4.Model)) he)
  have hlarge : 64 ≤ Nat.card (center P) :=
    hWcard ▸ Nat.card_le_card_of_injective wZ hwZ
  let := hK.2
  have hZR : q.ker ≤ R := by
    rw [hk]
    exact (D.sourceOrbit_binary_witness_ordinary_local_normalizers
      h hd F hF hmodel hw hWJ hJC K hK).1
  have hR := hc.ordinary_radical_intersection_isRadical K hK
  have hPne : P ≠ ⊥ := by
    intro he
    have hp : Nat.card (center P) ≤ 1 := by
      rw [he]
      exact le_of_eq Nat.card_unique
    omega
  have hPr : IsPRadical 2 P :=
    ⟨hPne,map_normalizer_core_of_p_kernel R hR.isPGroup hR.2 q hq hZR⟩
  have hNR : normalizer (R : Set K) ≤
      (H ⊓ normalizer (L : Set G)).comap j := by
    apply hc.ordinary_radical_normalizer_le_local_of_inner K hK
    intro a
    exact Janko4.perfect_cover_conj_surjective e a
  have hNB₀ : normalizer (R : Set K) ≤ normalizer (B₀ : Set K) :=
    (hNR.trans (comap_mono hn)).trans (LH.le_normalizer_comap j)
  have hNmap : (normalizer (R : Set K)).map q = N := by
    have hh : N.comap q = normalizer (R : Set K) := by
      rw [comap_normalizer_eq_of_surjective _ hq,comap_map_eq_self hZR]
    rw [←hh,map_comap_eq_self_of_surjective hq]
  have hNB : N ≤ normalizer (B : Set Janko4.Model) := by
    rw [←hNmap]
    exact (map_mono hNB₀).trans (B₀.le_normalizer_map q)
  have hB₀R : B₀ ≤ normalizer (R : Set K) :=
    (comap_mono ((le_conjugateSpanBy LH (H ⊓ normalizer (L : Set G))).trans
      hc.span_normalizes_radical)).trans ((J.pCoreIn 2).le_normalizer_comap j)
  have hBN : B ≤ N := (map_mono hB₀R).trans hNmap.le
  let BN := B.subgroupOf N
  let : BN.Normal := (normal_subgroupOf_iff_le_normalizer hBN).mpr hNB
  let a₁ : B₀ ≃* LH.subgroupOf H := subgroupOfEquivOfLe hLK
  let a : B₀ ≃* LH := a₁.trans (subgroupOfEquivOfLe hLH)
  let aq := QuotientGroup.congr (pCore 2 B₀) (pCore 2 LH) a (pCore_map_iso 2 a)
  obtain ⟨_,_,_,_,_,_,eL,_,_⟩ :=
    D.sourceOrbit_binary_witness_coordinates h hd F hF hmodel hw
  let f := q.subgroupMap B₀
  have hfp : IsPGroup 2 f.ker := by
    have he : f.ker = q.ker.subgroupOf B₀ := by ext x; exact Subtype.ext_iff
    rw [he,hk,IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot hc.oddCore_eq_bot K)]
    exact pCore_isPGroup.comap_subtype
  let eB : (B ⧸ pCore 2 B) ≃* BinaryLinearThree.Group :=
    (f.pCoreQuotientEquiv (q.subgroupMap_surjective B₀) hfp).symm.trans (aq.trans eL)
  let c : BN ≃* B := subgroupOfEquivOfLe hBN
  have hcp : (pCore 2 BN).map c.toMonoidHom = pCore 2 B :=
    @pCore_map_iso BN B inferInstance inferInstance 2 c
  let cq : (BN ⧸ pCore 2 BN) ≃* (B ⧸ pCore 2 B) :=
    QuotientGroup.congr _ _ c hcp
  exact Janko4.LocalStructure.LargeCenterRadicals.binaryThree_radical_false
    P hPr hlarge BN (cq.trans eB)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
