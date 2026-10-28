module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48OrdinaryLocal
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.InnerRadicalNormalizer
public import Theory.SpecificGroups.Rudvalis.ElementarySixtyFourRadicalNormalizer
public import Theory.SpecificGroups.Rudvalis.ComponentFacts
public import Theory.SpecificGroups.Rudvalis.Model.LocalStructure.BinaryThreeModules.Transitivity
public import Theory.Representation.PSL3Two.NaturalDualTransitiveObstruction

/-!
# The original doubled-binary ordinary component is not Rudvalis

The full original six-space injects through the component center and lies
in the center of the actual quotient radical. Native Rudvalis radical
control identifies that radical's normalizer with the full normalizer of
the six-space. Inner automorphisms of the perfect cover then make the
original residual normal in this full normalizer. Its literal natural-plus-
dual action contradicts the native transitivity on all 63 nonzero vectors.
No maximality, odd index, or trivial covering center is assumed.

Source: Aschbacher--Smith C.2.8, C.3.3--5 and C.4.8, pp.147,149--154,
and the native Rudvalis local inspection of 4.4.3, pp.622--623.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open BinaryLinearThree
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual whole natural-plus-dual orbit rules out the Rudvalis
central quotient through its full radical normalizer. -/
theorem sourceOrbit_binary_witness_ordinary_not_rudvalis
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : IsComponent H K) :
    ¬ Nonempty ((K ⧸ center K) ≃* Rudvalis.Model) := by
  rintro ⟨e⟩
  let j := H.subtype.comp K.subtype
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let R := (J.pCoreIn 2).comap j
  let W := D.sourceOrbit.comap j
  let B₀ := LH.comap j
  let P := R.map q
  let B := B₀.map q
  let N := normalizer (P : Set Rudvalis.Model)
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
    change (y : Rudvalis.Model) * q w = q w * y
    rw [←he]
    exact (q.map_mul r w).symm.trans ((congrArg q (hWC w.property r hr)).trans (q.map_mul w r))
  let wZ := wP.codRestrict (center P) hwPc
  have hwZ : Function.Injective wZ := by
    intro a b he
    exact hqi (congrArg (fun x : center P => ((x : P) : Rudvalis.Model)) he)
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
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
    obtain ⟨x,hx⟩ := Rudvalis.component_conj_surjective (MulAut.centralQuotientAction e a)
    obtain ⟨k,hk⟩ := (MulAut.centralQuotientAction_inner_iff e a).mp ⟨x,hx.symm⟩
    exact ⟨k,hk.symm⟩
  have hNB₀ : normalizer (R : Set K) ≤ normalizer (B₀ : Set K) :=
    (hNR.trans (comap_mono hn)).trans (LH.le_normalizer_comap j)
  have hNmap : (normalizer (R : Set K)).map q = N := by
    have hh : N.comap q = normalizer (R : Set K) := by
      rw [comap_normalizer_eq_of_surjective _ hq,comap_map_eq_self hZR]
    rw [←hh,map_comap_eq_self_of_surjective hq]
  have hNB : N ≤ normalizer (B : Set Rudvalis.Model) := by
    rw [←hNmap]
    exact (map_mono hNB₀).trans (B₀.le_normalizer_map q)
  have hB₀R : B₀ ≤ normalizer (R : Set K) :=
    (comap_mono ((le_conjugateSpanBy LH (H ⊓ normalizer (L : Set G))).trans
      hc.span_normalizes_radical)).trans ((J.pCoreIn 2).le_normalizer_comap j)
  have hBN : B ≤ N := (map_mono hB₀R).trans hNmap.le
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
  have hNE : N = normalizer (E₀ : Set Rudvalis.Model) :=
    (Rudvalis.radical_normalizer_eq_sixtyFour_normalizer P E₀ hPr hE₀card hE₀Z).2
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
  have htrans : ∀ x y : u.range, x ≠ 1 → y ≠ 1 →
      ∃ p : N, p.val * x.val * p.val⁻¹ = y.val := by
    rw [hur,hNE]
    exact Rudvalis.BinaryThreeModules.ElementarySixtyFour.normalizer_transitive E₀ hE₀card
  exact NaturalDual.no_transitive_mapped_conjugation f qB hqB u hu ha
    N hfN huN hfNormal huNormal htrans

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
