module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48OrdinaryLocal
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.RadicalPreservingInner
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.LargeCenterRadical
public import Theory.Representation.PSL3Two.NaturalDualNormalizerOrder
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MaximalLevi
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The original doubled-binary ordinary component is not PSL5(2)

The whole original six-space embeds centrally in the actual quotient
radical. Its order forces that radical to be the full unipotent radical of
a middle maximal parabolic. Automorphisms preserving this actual radical
are inner, which places its full normalizer in the original local subgroup.
The normal residual's marked natural-plus-dual action then forces the
parabolic order to be prime to nine, contradicting its literal Levi factors.
The covering center, actual radical and whole module are retained.

Source: Aschbacher--Smith C.2.7--8, C.3.3--5 and C.4.8, pp.145--154,
and the natural-plus-dual module inspection of 4.4.12, pp.621--622.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open BinaryLinearThree
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveFlagGeometry.MaximalOvergroups
private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual large-center radical and whole natural-plus-dual module
exclude the linear-five central quotient. -/
theorem sourceOrbit_binary_witness_ordinary_not_linear_five
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : IsComponent H K) :
    ¬ ClassicalGroup.IsPSL (K ⧸ center K) 5 2 := by
  rintro ⟨k,_,_,hk,⟨mk⟩⟩
  let := Fintype.ofFinite k
  let ak : k ≃+* ZMod 2 := (ZMod.ringEquivOfPrime k Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hk)).symm
  let e := mk.trans ((Atlas.fieldEquivPSL 5 ak).trans
    (projectiveEquivLinear (by decide : 0 < 5)))
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let R := (J.pCoreIn 2).comap j
  let W := D.sourceOrbit.comap j
  let B₀ := LH.comap j
  let P := R.map q
  let B := B₀.map q
  let N := normalizer (P : Set (LinearGroup 5))
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
    change (y : LinearGroup 5) * q w = q w * y
    rw [←he]
    exact (q.map_mul r w).symm.trans ((congrArg q (hWC w.property r hr)).trans (q.map_mul w r))
  let wZ := wP.codRestrict (center P) hwPc
  have hwZ : Function.Injective wZ := by
    intro a b he
    exact hqi (congrArg (fun x : center P => ((x : P) : LinearGroup 5)) he)
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
  let E₀ := W.map q
  let : IsElementaryAbelian 2 W :=
    IsElementaryAbelian.of_injective bW.toMonoidHom bW.injective
  let : IsElementaryAbelian 2 E₀ := IsElementaryAbelian.map q
  have hqWr : (q.comp W.subtype).range = E₀ := by
    rw [MonoidHom.range_comp,range_subtype]
  have hE₀card : Nat.card E₀ = 64 := by
    let ew : W ≃* E₀ := (MonoidHom.ofInjective hqi).trans (MulEquiv.subgroupCongr hqWr)
    exact (Nat.card_congr ew.toEquiv).symm.trans hWcard
  have hE₀Z : E₀ ≤ (center P).map P.subtype := by
    rintro z ⟨w,hw,rfl⟩
    exact ⟨wP ⟨w,hw⟩,hwPc ⟨w,hw⟩,rfl⟩
  obtain ⟨hPE,b,i,hi,hPrad,hNflag⟩ :=
    radical_eq_middle_of_central_sixtyFour P E₀ hPr hE₀card hE₀Z
  have hNE : N = normalizer (E₀ : Set (LinearGroup 5)) := by
    change normalizer (P : Set (LinearGroup 5)) = _
    rw [hPE]
  have hNR : normalizer (R : Set K) ≤
      (H ⊓ normalizer (L : Set G)).comap j := by
    apply hc.ordinary_radical_normalizer_le_local_of_preserving_inner K hK e
    change ∀ a : MulAut (LinearGroup 5), P.map a.toMonoidHom = P →
      a ∈ MulAut.innerSubgroup (LinearGroup 5)
    intro a ha
    exact radical_preserving_is_inner_of_central_sixtyFour P E₀ hPr hE₀card hE₀Z a ha
  have hNB₀ : normalizer (R : Set K) ≤ normalizer (B₀ : Set K) :=
    (hNR.trans (comap_mono hn)).trans (LH.le_normalizer_comap j)
  have hNmap : (normalizer (R : Set K)).map q = N := by
    have hh : N.comap q = normalizer (R : Set K) := by
      rw [comap_normalizer_eq_of_surjective _ hq,comap_map_eq_self hZR]
    rw [←hh,map_comap_eq_self_of_surjective hq]
  have hNB : N ≤ normalizer (B : Set (LinearGroup 5)) := by
    rw [←hNmap]
    exact (map_mono hNB₀).trans (B₀.le_normalizer_map q)
  have hB₀R : B₀ ≤ normalizer (R : Set K) :=
    (comap_mono ((le_conjugateSpanBy LH (H ⊓ normalizer (L : Set G))).trans
      hc.span_normalizes_radical)).trans ((J.pCoreIn 2).le_normalizer_comap j)
  have hBN : B ≤ N := (map_mono hB₀R).trans hNmap.le
  let a₁ : B₀ ≃* LH.subgroupOf H := subgroupOfEquivOfLe hLK
  let a : B₀ ≃* LH := a₁.trans (subgroupOfEquivOfLe hLH)
  obtain ⟨_,_,_,_,_,_,eL,_,E,hE,_,_⟩ :=
    D.sourceOrbit_binary_witness_coordinates h hd F hF hmodel hw
  let v₀ : Multiplicative NaturalDual.Space ≃* D.sourceOrbit :=
    E.symm.toAddEquiv.toMultiplicative.trans MulEquiv.toMultiplicative_toAdditive
  let v : Multiplicative NaturalDual.Space ≃* W := v₀.trans bW.symm
  have hv (x : Multiplicative NaturalDual.Space) : j (v x) = v₀ x := by
    exact congrArg (fun z : D.sourceOrbit => (z : G)) (bW.apply_symm_apply (v₀ x))
  let f := q.comp B₀.subtype
  let qB := (eL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 LH))).comp a.toMonoidHom
  have hqB : Function.Surjective qB :=
    (eL.surjective.comp (QuotientGroup.mk'_surjective _)).comp a.surjective
  let u := (q.comp W.subtype).comp v.toMonoidHom
  have hu : Function.Injective u := hqi.comp v.injective
  have hfr : f.range = B := by rw [MonoidHom.range_comp,range_subtype]
  have hur : u.range = E₀ := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr v.surjective,
      ←MonoidHom.range_eq_map,hqWr]
  have ha (r : B₀) (x : NaturalDual.Space) :
      f r * u (Multiplicative.ofAdd x) * (f r)⁻¹ =
        u (Multiplicative.ofAdd (NaturalDual.action (qB r) x)) := by
    have hact : doubledSeedAction LH D.sourceOrbit
        (((map_subtype_le _).trans inf_le_left).trans D.sourceOrbit_component_normalizes)
        (a r) (E.symm x) = E.symm (NaturalDual.action (qB r) x) := by
      apply E.injective
      rw [hE,E.apply_symm_apply,E.apply_symm_apply]
      rfl
    have hh : (r : K) * (v (Multiplicative.ofAdd x) : K) * (r : K)⁻¹ =
        (v (Multiplicative.ofAdd (NaturalDual.action (qB r) x)) : K) := by
      apply hj
      simp only [map_mul,map_inv,hv]
      exact congrArg (fun w : Additive D.sourceOrbit => (w.toMul : G)) hact
    change q (r : K) * q (v (Multiplicative.ofAdd x) : K) * (q (r : K))⁻¹ =
      q (v (Multiplicative.ofAdd (NaturalDual.action (qB r) x)) : K)
    simpa only [map_mul,map_inv] using congrArg q hh
  have hfN : f.range ≤ N := hfr ▸ hBN
  have huN : u.range ≤ N := by rw [hur,hNE]; exact le_normalizer
  have hfNormal : (f.range.subgroupOf N).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hfN).mpr
    rwa [hfr]
  have huNormal : (u.range.subgroupOf N).Normal := by
    rw [hur,hNE]
    exact normal_in_normalizer
  have hC : IsPGroup 2 (centralizer (u.range : Set (LinearGroup 5))) := by
    rw [hur,←hPE,hPrad]
    exact (radical_two (flagSpace b i)).to_le
      (centralizer_radical_le (flagSpace_ne_bot b i) (flagSpace_ne_top b i))
  have hnot := NaturalDual.not_nine_mapped_conjugation f qB hqB u hu ha
    N hfN huN hfNormal huNormal hC
  apply hnot
  change 9 ∣ Nat.card (normalizer (P : Set (LinearGroup 5)))
  rw [hNflag]
  apply dvd_trans _ (card_quotient_dvd_card (pCore 2 (flagStabilizer b {i})))
  rw [Nat.card_congr (singletonQuotientEquiv b i).toEquiv,Nat.card_prod]
  have hcard (n : ℕ) : Nat.card (LinearGroup n) = ∏ j : Fin n, (2^n - 2^j.val) := by
    rw [←Nat.card_congr (matrixEquivLinear n).toEquiv,Matrix.card_GL_field]
    simp
  rw [hcard,hcard]
  rcases hi with rfl | rfl <;> decide

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
