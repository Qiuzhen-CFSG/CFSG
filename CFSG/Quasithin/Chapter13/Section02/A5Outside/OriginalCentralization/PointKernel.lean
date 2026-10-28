module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointComponent
public import Theory.SpecificGroups.Alternating.FourCentralCover
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.MinimalParabolic

/-!
# Eliminating the original point residual's central two-kernel

The complementary point centralizes the common Baumann subgroup and its
three local conjugates multiply to one. Modulo the local two-residual its
image is central, so that identity puts it in the residual. It also lies
in the original elementary omega orbit. In the outside-core branch it
detects a nontrivial image under the proved central cover onto A₄.

The normal elementary detector and transfer kill the covering kernel.
The resulting A₄ equivalence gives the actual A₃-block module, contradicting
13.2.11(6) in SourceAssembly/PointKernel. This closes the outside-core
subcase of 13.2.12 without assuming the printed residual isomorphism.

The FF core branch, nonsolvable generation bound and single-factor endgame
remain with qt-d-1367-assembly. Earlier Context, 13.3.2, C.1.32 and 5.2.3
retain their producers, with final discharge at qt-d-1361-source.

Source: Aschbacher--Smith 13.2.11(6), 13.2.12, printed pp.881--883.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section06.CentralizerReduction Section06.CentralizerReduction.A5Module Stellmacher
private theorem triple_mem_residual {D : Type*} [Group D]
    (S : Subgroup D) (hgen : pResidual 2 D ⊔ S = ⊤)
    (x : D) (hcent : x ∈ centralizer (S : Set D))
    (hpow : x^2=1)
    (ht : ∃ a b : D, x * MulAut.conj a x * MulAut.conj b x = 1) :
    x ∈ pResidual 2 D := by
  let q := QuotientGroup.mk' (pResidual 2 D)
  have hqS : S.map q = ⊤ := by
    have hh := congrArg (map q) hgen
    simpa only [q,Subgroup.map_sup,QuotientGroup.map_mk'_self,bot_sup_eq,
      map_top_of_surjective q (QuotientGroup.mk'_surjective _)] using hh
  have hqc : q x ∈ center (D ⧸ pResidual 2 D) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨s,hs,rfl⟩ := hqS.ge (mem_top y)
    rw [←map_mul,←map_mul,mem_centralizer_iff.mp hcent s hs]
  have hconj (a : D) : q (MulAut.conj a x) = q x := by
    simp only [MulAut.conj_apply,map_mul,map_inv]
    rw [mem_center_iff.mp hqc,mul_inv_cancel_right]
  obtain ⟨a,b,ht⟩ := ht
  have hh := congrArg q ht
  simp only [map_mul,map_one,hconj] at hh
  have hx2 : q x * q x = 1 := by rw [←map_mul,←pow_two,hpow,map_one]
  rw [hx2,one_mul] at hh
  exact (QuotientGroup.eq_one_iff x).mp hh

private theorem block_of_equiv_four {E : Type*} [Group E] [Finite E]
    (e : E ≃* alternatingGroup (Fin 4)) :
    CFSG.Quasithin.ChapterC.IsAlternatingBlock E 3 := by
  have hp4 : IsPPerfect 2 (alternatingGroup (Fin 4)) := by
    rw [← Equiv.Perm.twoResidual_eq_alternating]
    exact isPPerfect_pResidual 2
  have hp := hp4.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hcore : (pCore 2 E).map e.toMonoidHom = alternatingGroup.kleinFour (Fin 4) :=
    (pCore_map_iso 2 e).trans AlternatingFourPair.twoCore_eq_kleinFour
  have hcard : Nat.card (pCore 2 E) = 4 := by
    calc
      Nat.card (pCore 2 E) = Nat.card ((pCore 2 E).map e.toMonoidHom) :=
        (card_map_of_injective e.injective).symm
      _ = 4 := by
        rw [hcore]
        exact alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num)
  let hfour := alternatingGroup.kleinFour_isKleinFour (by norm_num : Nat.card (Fin 4)=4)
  let : IsElementaryAbelian 2 (alternatingGroup.kleinFour (Fin 4)) := {
    toIsMulCommutative := hfour.isMulCommutative
    exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  let eU := (e.subgroupMap (pCore 2 E)).trans (MulEquiv.subgroupCongr hcore)
  have hel : IsElementaryAbelian 2 (pCore 2 E) :=
    IsElementaryAbelian.of_injective eU.toMonoidHom eU.injective
  have hc : Nat.card E = 12 := (Nat.card_congr e.toEquiv).trans
    (alternatingGroup.card_of_card_eq_four (by norm_num))
  have hq : Nat.card (E ⧸ pCore 2 E) = 3 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (pCore 2 E)
    rw [hc,hcard] at hh
    omega
  exact CFSG.Quasithin.ChapterC.RankOne.Solvable.MinimalParabolic.alternatingThree_of_elementary_four_core
    hp hel hcard hq

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)

/-- An outside-core complementary point forces the actual first local
two-residual to be an A₃ block. The elementary detecting subgroup is
the original omega orbit restricted through the literal inclusions. -/
theorem point_residual_block_of_complement_not_mem_core
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {P₁ : Subgroup G} (horiginal : IsOriginalPairedPointGroup d hH P₁)
    (hPH : P₁ ≤ H)
    (hBP : ChapterB.baumann (T : Subgroup G) ≤ P₁)
    (hJv : P₁ ⊔ (Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)) ≤
      Gv (markedV d.flag.flag.module)) :
    let P₂ := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
    let J := P₁ ⊔ P₂
    let A := P₁.subgroupOf J
    let B := P₂.subgroupOf J
    let q := QuotientGroup.mk' (pPrimeCore 3 J)
    P₁ ⊓ P₂ = ChapterB.baumann (T : Subgroup G) →
    IsSQTK KnownSimple.IsKnownSimple J →
    ChapterF.IsGoldschmidtTriple A B →
    ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) →
    A.map q ⊓ B.map q = ((ChapterB.baumann (T : Subgroup G)).subgroupOf J).map q →
    markedZ d.flag.flag.module * markedV d.flag.flag.module ∉ J.pCoreIn 2 →
    ChapterC.IsAlternatingBlock (pResidual 2 P₁) 3 := by
  intro P₂ J A B q hi hSQ hg hqg hqi hout
  let s := d.flag.flag.module
  let R := ChapterB.baumann (T : Subgroup G)
  have hzR := singular_mem_baumann d hH hB hZ hs hz
  have hvR := point_mem_baumann d hH hB hZ hs hz
  have haR : markedZ s * markedV s ∈ R := R.mul_mem hzR hvR
  let x : J := ⟨markedZ s * markedV s,mem_sup_left (hBP haR)⟩
  have hx : (x:G) = markedZ s * markedV s := rfl
  have hxA : x ∈ A := by
    change (x:G) ∈ P₁
    rw [hx]
    exact hBP haR
  let a : A := ⟨x,hxA⟩
  let S := (A ⊓ B).subgroupOf A
  have haC : a ∈ centralizer (S : Set A) := by
    intro y hy
    apply Subtype.ext
    apply Subtype.ext
    change ((y:A):J).val * (x:G) = (x:G) * ((y:A):J).val
    rw [hx]
    exact mem_centralizer_iff.mp (complement_centralizes_baumann d hH hB hZ hs hz)
      (((y:A):J):G) (hi ▸ hy)
  have hzV₁ : markedZ s ∈ V₁ := by
    rw [←d.flag.flag.line_eq]
    exact mem_zpowers _
  have ha2 : a^2=1 := by
    apply Subtype.ext
    apply Subtype.ext
    change (x:G)^2=1
    rw [hx]
    let := d.elementary
    exact elemPow_eq_one_of_isElementaryAbelian (p:=2) (markedZ s * markedV s)
      (V.mul_mem (d.flag.two_le_V (d.flag.one_le_two hzV₁))
        (d.flag.two_le_V d.flag.flag.vector_mem))
  have hgen : pResidual 2 A ⊔ S = ⊤ := by
    apply map_injective A.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le inf_le_left,
      ←MonoidHom.range_eq_map,range_subtype]
    exact hg.left_residual_sup_intersection
  have haD : a ∈ pResidual 2 A := triple_mem_residual S hgen a haC ha2 (by
    obtain ⟨u,hu,v,hv,ht⟩ := original_point_complement_three_conjugates d hH hB hZ hs hz horiginal
    let u' : A := ⟨⟨u,mem_sup_left hu⟩,hu⟩
    let v' : A := ⟨⟨v,mem_sup_left hv⟩,hv⟩
    refine ⟨u',v',?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change (x:G) * MulAut.conj u (x:G) * MulAut.conj v (x:G) = 1
    rwa [hx])
  let U := (omegaOrbit T H).subgroupOf H
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let := hU.elementary
  let j : A →* H := (inclusion hPH).comp
    (subgroupOfEquivOfLe (show P₁ ≤ J from le_sup_left)).toMonoidHom
  let D := pResidual 2 A
  let k : D →* H := j.comp D.subtype
  let W := U.comap k
  let : W.Normal := inferInstance
  have hk : Function.Injective k := (inclusion_injective hPH).comp
    ((subgroupOfEquivOfLe (show P₁ ≤ J from le_sup_left)).injective.comp D.subtype_injective)
  let w : W →* U := (k.comp W.subtype).codRestrict U (fun y => y.property)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective w
    (by intro y z he; apply Subtype.ext; exact hk (congrArg Subtype.val he))
  have hV₂U : V₂ ≤ omegaOrbit T H :=
    (source_alpha_eq_flag_plane d hH hB hZ hs hz).symm.le.trans
      ((source_alpha_eq_omegaOrbit_fixed d hH hB hZ hs hz).le.trans inf_le_left)
  have haW : (⟨a,haD⟩ : D) ∈ W := by
    change (x:G) ∈ omegaOrbit T H
    rw [hx]
    exact hV₂U (V₂.mul_mem (d.flag.one_le_two hzV₁)
      d.flag.flag.vector_mem)
  obtain ⟨f,hf,hfker,hf2,hfc⟩ := point_residual_central_covers_of_complement_not_mem_core
    d hH hB hZ hs hz horiginal hBP hJv hi hSQ hg hqg hqi hout A (Or.inl rfl)
  have him : W.map f ≠ ⊥ := by
    intro he
    have hfa : f ⟨a,haD⟩ = 1 := mem_bot.mp (he ▸ mem_map_of_mem f haW)
    have haQ : x ∈ pCore 2 J := by
      change (⟨a,haD⟩ : D) ∈ ((pCore 2 J).subgroupOf A).subgroupOf D
      rw [←hfker]
      exact hfa
    exact hout (hx ▸ mem_map_of_mem J.subtype haQ)
  have hfi := alternatingGroup.four_cover_injective_of_normal_elementary_image f hf (isPPerfect_pResidual 2) hf2 hfc W him
  have hbD := block_of_equiv_four (MulEquiv.ofBijective f ⟨hfi,hf⟩)
  let eA : A ≃* P₁ := subgroupOfEquivOfLe le_sup_left
  let eD : D ≃* pResidual 2 P₁ :=
    (eA.subgroupMap D).trans (MulEquiv.subgroupCongr (map_pResidual 2 eA))
  exact ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv eD hbD
end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
