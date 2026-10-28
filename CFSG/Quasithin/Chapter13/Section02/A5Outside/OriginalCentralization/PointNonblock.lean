module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointAmalgam
public import CFSG.Quasithin.Chapter13.Section09.Source
public import Theory.SpecificGroups.Alternating.FourPairAutomorphisms
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.Source
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree.CubicPair
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import Theory.GroupTheory.PResidual.NormalSup
public import Theory.SpecificGroups.SymmetricThree.CubicSelection
public import Theory.GroupTheory.PResidual.NormalPGroupSupplement

/-!
# The original paired point residual is not an A₃ block

For a center-free solvable outside group H, its two-residual R has a maximal
two-local normalizer N. The kernel of the action of N on R intersects O₂(N)
trivially, since the original Sylow centralizer of R vanishes. Characteristic
two then makes this action faithful. If R were A₄ × A₄, its automorphism
group would be S₄ wr C₂; the original quotient order and the residual core
order force N to be that full group, contradicting the proved 13.9.1.

If one original S₃ factor preimage has an A₃-block residual, Sylow conjugacy
makes both residuals A₃ blocks. They are distinct subnormal cubic blocks,
so C.1.9 makes them commute; their join is the full residual of H. This
would give the excluded A₄ × A₄ model. Adjoining the normalizing two-group
Baum(T) preserves the embedded residual, so the exclusion applies to the
literal first point group in 13.2.12, with its original factor preimage.

The last theorem applies to the contrary core-free Borel join; its universal
terminal application is in SourceAssembly/PointNonblock. This supplies the
13.2.11(6) input. The A₅ nonblock and equal-core arguments, the F.6.18
exclusions, nonsolvable generation bound and single-factor endgame remain
with qt-d-1367-assembly; no full 13.2.7 is claimed here.

Source: Aschbacher--Smith 13.2.11(6) and 13.2.12, printed pp.881--883;
13.9.1, printed pp.969--974; C.1.9, printed pp.123--124.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization

private theorem preimage_conjugate {X Q : Type*} [Group X] [Group Q]
    (q : X →* Q) (A : Subgroup Q) (t : X) :
    (A.comap q).map (MulAut.conj t).toMonoidHom =
      (A.map (MulAut.conj (q t)).toMonoidHom).comap q := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨q a,ha,by simp [MulAut.conj_apply]⟩
  · rintro ⟨a,ha,he⟩
    refine ⟨t⁻¹*x*t,?_,by simp [MulAut.conj_apply,mul_assoc]⟩
    change q (t⁻¹*x*t) ∈ A
    rw [map_mul,map_mul,map_inv,←he]
    simpa [MulAut.conj_apply,mul_assoc] using ha

private theorem factorResidual_pair_model
    {X Q W : Type*} [Group X] [Finite X] [Group Q] [Finite Q]
    [AddCommGroup W] [Module (ZMod 2) W]
    (q : X →* Q) (hq : Function.Surjective q)
    {ρ : Representation (ZMod 2) Q W} (c : ChapterB.SolvableFFFactors ρ)
    (hc : c.count = 2)
    (ht : ∀ i j, ∃ t : X, (c.factor i).map (MulAut.conj (q t)).toMonoidHom = c.factor j)
    (hr : pResidual 2 Q ≤ offenderSubgroup ρ)
    (hself : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    (i : Fin c.count)
    (hb : ChapterC.IsAlternatingBlock (pResidual 2 ((c.factor i).comap q)) 3) :
    Nonempty (pResidual 2 X ≃* AlternatingFourPair.Model) := by
  let A := fun k => (c.factor k).comap q
  let K := fun k => (pResidual 2 (A k)).map (A k).subtype
  have hconj (j k) : ∃ t : X, (K j).map (MulAut.conj t).toMonoidHom = K k := by
    obtain ⟨t,ht⟩ := ht j k
    refine ⟨t,?_⟩
    rw [map_embedded_pResidual,preimage_conjugate q,ht]
  have hblock (k) : ChapterC.IsAlternatingBlock (K k) 3 := by
    obtain ⟨t,ht⟩ := hconj i k
    let e := ((pResidual 2 (A i)).equivMapOfInjective (A i).subtype (A i).subtype_injective).trans
      (((K i).equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective).trans
        (MulEquiv.subgroupCongr ht))
    exact ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv e hb
  let := offenderSubgroup_normal ρ
  have hsub (k) : (K k).IsSubnormal := by
    have hn : (c.factor k).IsSubnormal := .step _ _ (c.factor_le_offenderSubgroup k)
      (inferInstance : (offenderSubgroup ρ).Normal).isSubnormal
      (c.factor_normal_in_offenderSubgroup k)
    exact (inferInstance : (pResidual 2 (A k)).Normal).isSubnormal.trans' (hn.comap q)
  let j : Fin c.count := ⟨0,by omega⟩
  let k : Fin c.count := ⟨1,by omega⟩
  have hjk : j ≠ k := by intro he; have := congrArg Fin.val he; simp [j,k] at this
  have hfactor : c.factor j ⊔ c.factor k = offenderSubgroup ρ := by
    rw [←c.iSup_factor]
    apply le_antisymm (sup_le (le_iSup _ j) (le_iSup _ k))
    apply iSup_le
    intro a
    have he : a = j ∨ a = k := by
      have ha := a.isLt
      have he : a.val = 0 ∨ a.val = 1 := by omega
      rcases he with he | he
      · exact Or.inl (Fin.ext he)
      · exact Or.inr (Fin.ext he)
    rcases he with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  have hA : A j ⊔ A k = (offenderSubgroup ρ).comap q := by
    change (c.factor j).comap q ⊔ (c.factor k).comap q = _
    rw [comap_sup_eq q _ _ hq,hfactor]
  have hn (a : Fin c.count) : A j ⊔ A k ≤ normalizer (A a : Set X) := by
    rw [hA]
    exact (comap_mono ((normal_subgroupOf_iff_le_normalizer
      (c.factor_le_offenderSubgroup a)).mp (c.factor_normal_in_offenderSubgroup a))).trans
      (le_normalizer_comap q)
  let : ((A j).subgroupOf (A j ⊔ A k)).Normal := normal_subgroupOf_of_le_normalizer (hn j)
  let : ((A k).subgroupOf (A j ⊔ A k)).Normal := normal_subgroupOf_of_le_normalizer (hn k)
  have hR : K j ⊔ K k = pResidual 2 X := by
    apply embedded_pResidual_sup_eq_of_contains_residual 2 (A j) (A k)
    rw [hA]
    exact ((map_le_iff_le_comap.mp (map_pResidual_le 2 q)).trans (comap_mono hr))
  have hKimage (a) : (K a).map q =
      (pResidual 2 (c.factor a)).map (c.factor a).subtype := by
    rw [map_embedded_pResidual,map_comap_eq_self_of_surjective hq]
  have hne : K j ≠ K k := by
    intro he
    have hm := congrArg (map q) he
    rw [hKimage,hKimage] at hm
    have hzero : (pResidual 2 (c.factor j)).map (c.factor j).subtype = ⊥ := by
      apply bot_unique
      have hd := c.factors_independent.pairwiseDisjoint hjk
      exact (le_inf (map_subtype_le _) (hm ▸ map_subtype_le _)).trans hd.le_bot
    have hz : pResidual 2 (c.factor j) = ⊥ :=
      (map_eq_bot_iff_of_injective _ (c.factor j).subtype_injective).mp hzero
    obtain ⟨es⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    let e := (c.factorModel j).trans es
    have hm := map_pResidual_of_surjective 2 e.toMonoidHom e.surjective
    rw [hz,Subgroup.map_bot] at hm
    have hh := Theory.SpecificGroups.SymmetricThree.CubicSelection.residual_card
    rw [←hm,card_bot] at hh
    omega
  have hq (a) : Nat.card (K a ⧸ pCore 2 (K a)) = 3 := by
    obtain ⟨e⟩ := (hblock a).2.2.quotient_iso
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    rfl
  have hcomm := ChapterC.BlockCommutation.cubic_blocks_commute_of_selfCentralizing
    hself (K j) (K k) ⟨inferInstance,(hblock j).2.1,hsub j⟩
      ⟨inferInstance,(hblock k).2.1,hsub k⟩ (hq j) (hq k) hne
  obtain ⟨_,⟨e⟩,_⟩ := ChapterC.alternatingThree_pair (K j) (K k) (hblock j) (hblock k)
    (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  exact ⟨(MulEquiv.subgroupCongr hR).symm.trans e⟩


variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- Characteristic two and the original residual Sylow centralizer make
the maximal local normalizer act faithfully on the full residual. -/
theorem paired_residual_normalizer_faithful
    (hn : ∀ K ∈ MainForward.faithfulLocalComponents T,
      (T : Subgroup G) ≤ normalizer (K : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    Function.Injective ((pResidual 2 H).map H.subtype).normalizerMonoidHom := by
  let R := (pResidual 2 H).map H.subtype
  let N := normalizer (R : Set G)
  obtain ⟨e⟩ := (source_centerfree_residual_core_quotient_models d hH hB hZ hs hz).1
  have hmax := (source_wreath_residual_normalizer_unique_of_normalizes_faithful
    d hn hH hB hZ hs e).1
  have hHN : H ≤ N := by
    have hh := (pResidual 2 H).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hTN := hH.1.1.2.trans hHN
  have hchar := d.hypothesis.qtke.evenCharacteristic T N hmax hTN
  let C := R.normalizerMonoidHom.ker
  have hdis : C ⊓ pCore 2 N = ⊥ := by
    apply bot_unique
    intro x hx
    have hxc : (x : G) ∈ centralizer (R : Set G) := by
      have hh := hx.1
      change x ∈ R.normalizerMonoidHom.ker at hh
      rwa [normalizerMonoidHom_ker] at hh
    have hxt : (x : G) ∈ (T : Subgroup G) :=
      pCore_isPGroup.le_sylow_of_normal (T.subtype hTN) hx.2
    have hh := source_residual_sylow_centralizer_eq_bot T H hH.1.1.2 hz
    have he : (x : G) = 1 := hh.le ⟨hxt,hxc⟩
    exact Subtype.ext he
  have hc : C ≤ pCore 2 N := by
    apply le_trans ?_ hchar
    apply commutator_eq_bot_iff_le_centralizer.mp
    exact bot_unique ((commutator_le_inf C (pCore 2 N)).trans hdis.le)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  exact bot_unique ((le_inf le_rfl hc).trans hdis.le)

/-- An A₄ × A₄ residual forces its actual maximal local normalizer to be
the full S₄ wreath product, by faithfulness and the original orders. -/
theorem paired_residual_normalizer_wreath
    (hn : ∀ K ∈ MainForward.faithfulLocalComponents T,
      (T : Subgroup G) ≤ normalizer (K : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    (eR : pResidual 2 H ≃* AlternatingFourPair.Model) :
    Nonempty ((normalizer (((pResidual 2 H).map H.subtype) : Set G)) ≃*
      Section09.WreathModel) := by
  let R := (pResidual 2 H).map H.subtype
  let N := normalizer (R : Set G)
  let e : R ≃* AlternatingFourPair.Model :=
    ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).symm.trans eR
  let f : N →* Section09.WreathModel :=
    AlternatingFourPair.mulAut_equiv_regularWreath.toMonoidHom.comp
      ((MulAut.congr e).toMonoidHom.comp R.normalizerMonoidHom)
  have hf : Function.Injective f :=
    AlternatingFourPair.mulAut_equiv_regularWreath.injective.comp
      ((MulAut.congr e).injective.comp (paired_residual_normalizer_faithful d hn hH hB hZ hs hz))
  have hHN : H ≤ N := by
    have hh := (pResidual 2 H).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hcore : Nat.card (pCore 2 (pResidual 2 H)) = 16 := by
    rw [←card_map_of_injective (f := eR.toMonoidHom) eR.injective,pCore_map_iso]
    exact AlternatingFourPair.card_twoCore
  have hle : (pCore 2 (pResidual 2 H)).map (pResidual 2 H).subtype ≤ pCore 2 H :=
    le_sSup ⟨inferInstance,pCore_isPGroup.map _⟩
  have hcard : 16 ≤ Nat.card (pCore 2 H) := by
    have hh := card_le_of_le hle
    rwa [card_map_of_injective (pResidual 2 H).subtype_injective,hcore] at hh
  obtain ⟨eQ⟩ := (source_centerfree_residual_core_quotient_models d hH hB hZ hs hz).1
  have hQ : Nat.card (H ⧸ pCore 2 H) = 72 := by
    rw [Nat.card_congr eQ.toEquiv,RegularWreathProduct.card]
    obtain ⟨e3⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    rw [Nat.card_congr e3.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hHcard : 1152 ≤ Nat.card H := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 H),hQ]
    omega
  have hNcard : Nat.card Section09.WreathModel ≤ Nat.card N := by
    rw [AlternatingFourPair.symmetric_wreath_card]
    exact hHcard.trans (card_le_of_le hHN)
  exact ⟨MulEquiv.ofBijective f (hf.bijective_of_nat_card_le hNcard)⟩

/-- The proved source 13.9.1 excludes the A₄ × A₄ residual model. -/
theorem paired_residual_not_alternatingFour_pair
    (hn : ∀ K ∈ MainForward.faithfulLocalComponents T,
      (T : Subgroup G) ≤ normalizer (K : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    ¬ Nonempty (pResidual 2 H ≃* AlternatingFourPair.Model) := by
  rintro ⟨eR⟩
  obtain ⟨eN⟩ := paired_residual_normalizer_wreath d hn hH hB hZ hs hz eR
  obtain ⟨eQ⟩ := (source_centerfree_residual_core_quotient_models d hH hB hZ hs hz).1
  have hmax := (source_wreath_residual_normalizer_unique_of_normalizes_faithful
    d hn hH hB hZ hs eQ).1
  have hHN : H ≤ normalizer (((pResidual 2 H).map H.subtype) : Set G) := by
    have hh := (pResidual 2 H).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  exact Section09.false_of_maximal_wreath d.hypothesis.qtke T _ hmax
    (hH.1.1.2.trans hHN) eN


omit d in
private theorem residual_join_two
    (A B : Subgroup G) (hB : IsPGroup 2 B)
    (hn : B ≤ normalizer (A : Set G)) :
    (pResidual 2 (A ⊔ B : Subgroup G)).map (A ⊔ B).subtype =
      (pResidual 2 A).map A.subtype := by
  let J := A ⊔ B
  let : (A.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le A.le_normalizer hn)
  have hh := pResidual_of_normal_pGroup_supplement 2 (A.subgroupOf J) (B.subgroupOf J)
    hB.comap_subtype (by rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self])
  have hm := congrArg (map J.subtype) hh
  rw [map_embedded_pResidual,map_subgroupOf_eq_of_le le_sup_left] at hm
  exact hm.symm

/-- The two-residual of the actual first point group is not an A3 block.
The factor preimage in its construction is retained throughout. -/
theorem original_paired_point_residual_nonblock
    (hn : ∀ K ∈ MainForward.faithfulLocalComponents T,
      (T : Subgroup G) ≤ normalizer (K : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {P₁ : Subgroup G} (hOriginal : IsOriginalPairedPointGroup d hH P₁) :
    ¬ ChapterC.IsAlternatingBlock (pResidual 2 P₁) 3 := by
  let S := T.subtype hH.1.1.2
  let U := (omegaOrbit T H).subgroupOf H
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  obtain ⟨c,hc,ht,i,j,_,_,hP⟩ := hOriginal
  let D := c.toSolvableFFFactors
  let A := (c.factor i).comap q
  let F := A.map H.subtype
  let B := ChapterB.baumann (T : Subgroup G)
  obtain ⟨_,_,hp,_,hj⟩ := e23_hypotheses d.hypothesis.qtke T d.normalizes_L hH hB hZ
  have hne : q.ker ≠ ⊤ := by
    intro he
    apply hj
    rw [QuotientGroup.ker_mk'] at he
    exact le_top.trans he.ge
  have hpq := (ChapterB.minimalParabolic_reduced_image S hp q
    (QuotientGroup.mk'_surjective C) hU.quotient_pCore_eq_bot hne).2
  have hr := (ChapterB.offender_generation (S.mapSurjective (QuotientGroup.mk'_surjective C))
    hpq ρ ((isFFModule_iff_quadraticRatio_le_one ρ).mpr c.ratio_one.le)
      hU.quotient_pCore_eq_bot).1
  have hBq := (ChapterE.ThompsonAction.solvable_pair_images_of_factors S hp U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    hU.quotient_pCore_eq_bot (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S))
    hj c hc ht).2
  have hBm : (ChapterB.baumann (S : Subgroup H)).map H.subtype = B := by
    dsimp only [B, ChapterB.baumann, ChapterB.thompsonAlpha]
    rw [baumann_map_injective H.subtype H.subtype_injective,
      show (S : Subgroup H).map H.subtype = (T : Subgroup G) from
        map_subgroupOf_eq_of_le hH.1.1.2]
  have hBA : ChapterB.baumann (S : Subgroup H) ≤ normalizer (A : Set H) := by
    have hh : ChapterB.baumann (S : Subgroup H) ≤ (offenderSubgroup ρ).comap q := by
      intro b hb
      exact (hBq ▸ mem_map_of_mem q hb).2
    exact (hh.trans (comap_mono ((normal_subgroupOf_iff_le_normalizer
      (D.factor_le_offenderSubgroup i)).mp (D.factor_normal_in_offenderSubgroup i)))).trans
        (le_normalizer_comap q)
  have hBF : B ≤ normalizer (F : Set G) := by
    rw [←hBm]
    exact (map_mono hBA).trans (A.le_normalizer_map H.subtype)
  have hR : (pResidual 2 P₁).map P₁.subtype =
      ((pResidual 2 A).map A.subtype).map H.subtype := by
    rw [hP,residual_join_two _ _ (T.isPGroup'.to_le (show B ≤ T from inf_le_left)) hBF,
      map_embedded_pResidual]
  intro hb
  let f := H.subtype.comp A.subtype
  let e : pResidual 2 P₁ ≃* pResidual 2 A :=
    ((pResidual 2 P₁).equivMapOfInjective P₁.subtype P₁.subtype_injective).trans
      ((MulEquiv.subgroupCongr (hR.trans (map_map _ _ _))).trans
        ((pResidual 2 A).equivMapOfInjective f
          (H.subtype_injective.comp A.subtype_injective)).symm)
  have hblock := ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv e hb
  have hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
      (d.hypothesis.qtke.evenCharacteristic T) hH.1.1)
  have hmodel := factorResidual_pair_model q (QuotientGroup.mk'_surjective C) D hc
    (fun a b => by obtain ⟨t,ht⟩ := ht a b; exact ⟨(t : H),ht⟩) hr hself i hblock
  exact paired_residual_not_alternatingFour_pair d hn hH hB hZ hs hz hmodel

/-- Original 13.2.11(6) on the point group constructed in the contrary
core-free Borel join of 13.2.12. -/
theorem coreFree_borel_join_point_residual_nonblock
    (hn : ∀ K ∈ MainForward.faithfulLocalComponents T,
      (T : Subgroup G) ≤ normalizer (K : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hcore : (H ⊔ borelResidual T L).pCoreIn 2 = ⊥)
    {P₁ : Subgroup G} (hOriginal : IsOriginalPairedPointGroup d hH P₁) :
    ¬ ChapterC.IsAlternatingBlock (pResidual 2 P₁) 3 :=
  original_paired_point_residual_nonblock d hn hH hB hZ hs
    (center_eq_bot_of_borel_join_core_eq_bot d hH hZ hcore) hOriginal

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
