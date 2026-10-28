module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.NaturalPairDegree
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.CoverSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.FixedFreeFullSpan
public import Theory.SpecificGroups.SL2.OddRadicalConjugatePair
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
/-!
# Quasisimplicity of the full natural-block source span

The actual block image in X/O2(X) is binary PSL2 or SL2(5). A binary
image has two-rank at least two, excluding the noncentral-Fitting branch.
For SL2(5), that branch would supply a moving conjugate pair inside the
odd Fitting subgroup. Its actual two-core-free quotient acts faithfully
on U(K)+U(K)^g, of degree at most twelve, contradicting the genuine
noncentral-Fitting degree bound of fifteen. The proof lifts the chosen
conjugator into X and identifies both pair images explicitly.
No fixed-free central-layer or descended-action assumption is used.
The genuine universal A.3.12 implication remains an earlier source input.
Source: Aschbacher--Smith C.5.12, printed p.163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem quasisimple_of_cComponent_fitting_central {H : Type*} [Group H] [Finite H]
    {L : Subgroup H} (hL : L.IsCComponent) (hf : fittingSubgroup L ≤ center L) :
    IsQuasisimple L := by
  have hs : solvableRadical L = center L := by
    apply le_antisymm (solvableRadical_le_center_of_fitting_le_center hf)
    exact le_solvableRadical (center L) inferInstance
      (Group.isSolvable_of_comm (fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm))
  let := hL.perfect
  let := hL.isSimpleGroup_quotient_solvableRadical
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hs).symm.isSimpleGroup⟩

private theorem map_conjugate {H J : Type*} [Group H] [Group J]
    (f : H →* J) (B : Subgroup H) (g : H) :
    (B.conjBy g).map f = (B.map f).conjBy (f g) := by
  change (B.map (MulAut.conj g).toMonoidHom).map f =
    (B.map f).map (MulAut.conj (f g)).toMonoidHom
  rw [map_map,map_map]
  congr 1
  ext b
  change f (g*b*g⁻¹) = f g*f b*(f g)⁻¹
  simp only [map_mul,map_inv]

theorem natural_source_full_span_quotient_quasisimple
    {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK κ Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    {K T : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) {n : ℕ} (hn : IsL2EvenBlock K n)
    (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (X : Subgroup G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G)) :
    let D := conjugateSpanBy K X
    IsQuasisimple ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) := by
  have hK : IsChiZeroBlock K := Or.inl ⟨n,hn⟩
  have h3 : ¬ IsAlternatingBlock K 3 := by
    intro h3
    obtain ⟨E,_,_,hE,_,hm⟩ := hn.2.2
    obtain ⟨e⟩ := hm.quotient_iso
    obtain ⟨e3⟩ := h3.2.2.quotient_iso
    have hc : Nat.card (K ⧸ pCore 2 K) = 3 := by
      rw [Nat.card_congr e3.toEquiv,Nat.card_eq_fintype_card,card_alternatingGroup]
      decide
    have hle := Nat.card_le_card_of_injective (Matrix.SpecialLinearGroup.upperUnipotentHom E)
      (Matrix.SpecialLinearGroup.upperUnipotentHom_injective E)
    change Nat.card E ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) E) at hle
    rw [← Nat.card_congr e.toEquiv,hE,hc] at hle
    have hlo : 4 ≤ 2^n := Nat.pow_le_pow_right (by decide : 1≤2) hn.1
    omega
  have hKX : K ≤ X := le_sup_left.trans hAX
  have hUT : U K ≤ T := h.module_le.trans inf_le_left
  let V := conjugateSpanBy (U K) X
  let D := conjugateSpanBy K X
  have hVX : V ≤ X := conjugateSpanBy_le_self ((map_subtype_le _).trans hKX)
  have hr := noncubic_full_span_reduced K T hK h3 hUT hT hTK X hKX S hS hVC
  have hXH : X ∈ Chapter1.H G := by
    intro he
    have hU : U K = ⊥ := by
      apply bot_unique
      intro v hv
      have hcore : (⟨v,hVX ((le_conjugateSpanBy _ _) hv)⟩ : X) ∈ pCore 2 X :=
        hr.le_pCore ((le_conjugateSpanBy _ _) hv)
      exact he ▸ mem_map_of_mem X.subtype hcore
    exact hK.chi.short.blockU_ne_bot ((map_eq_bot_iff_of_injective (blockU K) K.subtype_injective).mp hU)
  let q := QuotientGroup.mk' (pCore 2 X)
  let B := (K.subgroupOf X).map q
  let E := (D.subgroupOf X).map q
  have hD := (EmbeddingSelection.source_larger_span_embedding hG hA312 K T X hK h3 hTK hAX hX S hS).1
  let := pCore_isNilpotent (p := 2) (G := X)
  have hE : E.IsCComponent := hD.map_quotient (pCore 2 X)
  have hBE : B ≤ E := map_mono (subgroupOf_mono X (le_conjugateSpanBy K X))
  have hsq := uniqueness_local_quotient_sqtk hG hXH
  have hO := pCore_quotient_pCore_eq_bot (G := X) 2
  obtain ⟨hB,m,hm,hbinary,hmodels⟩ := EmbeddingSelection.noncubic_twoCore_small_models
    K T X hK h3 hUT hT hTK hKX hX S hS hVC
  let : IsQuasisimple B := hB
  have hquasi : IsQuasisimple E := by
    rcases hmodels with hb | ⟨hm2,hb⟩
    · have hbr := EmbeddingSelection.binary_rank_lower hb
      exact ChapterA.Section03.NoncentralFitting.quasisimple_of_two_le_two_rank hsq hO hE
        ((by omega : 2≤m).trans (hbr.trans (primeRank_mono 2 hBE)))
    · have hnat : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^n) :=
        hn.2.2.choose_spec.choose_spec.choose_spec.2.1
      have hn2 : n=2 := (EmbeddingSelection.binary_two_valuation (lt_of_lt_of_le (by decide : 0<2) hn.1) hnat).symm.trans
        ((EmbeddingSelection.binary_two_valuation (by omega : 0<m) hbinary).trans hm2)
      have hn' : IsL2EvenBlock K 2 := hn2 ▸ hn
      apply quasisimple_of_cComponent_fitting_central hE
      by_contra hnot
      obtain ⟨hshape,hcommon⟩ := ChapterA.Section03.NoncentralFitting.structure_of_noncentral hsq hO hE hnot
      have hfg : generalizedFitting E = fittingSubgroup E := hshape.elim And.left And.left
      let N := fittingSubgroup E
      have hself : centralizer (N : Set E) ≤ N := by
        simpa only [hfg] using centralizer_generalizedFitting_le E
      have hodd : Odd (Nat.card N) := ChapterA.Section03.NoncentralFitting.fitting_odd_card hE hO
      let B0 := B.subgroupOf E
      obtain ⟨F0,_,_,hF0,⟨eB⟩⟩ := hb
      let e0 := (subgroupOfEquivOfLe hBE).trans eB
      obtain ⟨g,hg,hpair⟩ := OddRadicalConjugatePair.exists_sl2_five_pair_of_odd_nilpotent
        hF0 N B0 hodd hself e0
      let P := B0 ⊔ B0.conjBy g
      let : Finite P := inferInstance
      change pCore 2 P=⊥ ∧ Group.IsPerfect P ∧ (⊤ : Subgroup P).IsCComponent ∧
        IsSimpleGroup (P ⧸ solvableRadical P) ∧ ¬IsMulCommutative (P ⧸ solvableRadical P) ∧
        ¬ fittingSubgroup P ≤ center P at hpair
      obtain ⟨x,hx⟩ := q.subgroupMap_surjective (D.subgroupOf X) g
      have hx' : q x.val = g.val := congrArg Subtype.val hx
      let A := (K.subgroupOf X) ⊔ (K.subgroupOf X).conjBy x.val
      have hmap : P.map E.subtype = A.map q := by
        rw [Subgroup.map_sup,Subgroup.map_sup,map_conjugate,map_conjugate,map_subgroupOf_eq_of_le hBE,hx']
        rfl
      let ep := (P.equivMapOfInjective E.subtype E.subtype_injective).trans (MulEquiv.subgroupCongr hmap)
      have hOp : pCore 2 (A.map q)=⊥ := by
        rw [← pCore_map_iso 2 ep,hpair.1,Subgroup.map_bot]
      have hCp : (⊤ : Subgroup (A.map q)).IsCComponent := by
        simpa only [map_top_of_surjective ep.toMonoidHom ep.surjective] using hpair.2.2.1.map_equiv ep
      have hf := natural_source_pair_image_fitting_central hG h hn' hT hTK X hKX hX S hS hVC
        x.val hOp ⊤ hCp
      let : IsQuasisimple (⊤ : Subgroup (A.map q)) := quasisimple_of_cComponent_fitting_central hCp hf
      let : IsQuasisimple (A.map q) := IsQuasisimple.of_mulEquiv topEquiv
      let : IsQuasisimple P := IsQuasisimple.of_mulEquiv ep.symm
      let : Group.IsNilpotent (fittingSubgroup P) := fittingSubgroup_nilpotent
      let : Group.IsSolvable (fittingSubgroup P) := IsNilpotent.to_isSolvable
      exact hpair.2.2.2.2.2 ((le_solvableRadical (fittingSubgroup P) inferInstance inferInstance).trans
        IsQuasisimple.solvableRadical_le_center)
  let f := q.subgroupMap (D.subgroupOf X)
  have hk : f.ker = pCore 2 (D.subgroupOf X) := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hD.subnormal).symm
  let eD := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f (q.subgroupMap_surjective _))
  let := hquasi
  exact IsQuasisimple.of_mulEquiv eD.symm
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
