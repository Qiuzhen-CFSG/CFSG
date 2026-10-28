module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointNonblock
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveCentralizer
public import CFSG.Quasithin.ChapterC.Section01.LocalCoreDisplacement
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.FactorPreimage
public import Theory.GroupTheory.SylowNormalIntersectionIndex

/-!
# The original local component is not an A₅ block

An A₅ block would split O₂(LT) into its natural sixteen-group and its
centralizer. Source 13.2.11(1) kills that centralizer. The actual S₅ local
action gives |T|=128; the original S₃ wreath quotient then gives |O₂(H)|=16.
The two natural factor supports already supply sixteen elements in U_H,
so O₂(H)=U_H. Each original factor preimage now has an A₃-block residual,
contradicting the proved 13.2.11(6) exclusion.

The same original point-group witness is retained when adjoining Baum(T).
The final theorem applies to the contrary core-free Borel join of 13.2.12;
SourceAssembly/FiveNonblock supplies it to the universal terminal consumer.
The equal-core argument, F.6.18 exclusions, nonsolvable generation bound
and single-factor endgame remain with qt-d-1367-assembly.

Source: Aschbacher--Smith 13.2.11(5)--(6), printed p.881, and the opening
of 13.2.12, printed pp.881--882.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- The A₅ block splitting and the actual Sylow centralizer give the local core order. -/
theorem block_local_core_card
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    (hb : ChapterC.IsAlternatingBlock L 5) :
    Nat.card (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) = 16 := by
  have hsplit := hb.normalizer_twoCore_eq_module_sup_centralizer
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
    (sup_le L.le_normalizer d.normalizes_L)
  have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    exact map_le_iff_le_comap.mpr
      (pCore_isPGroup.le_sylow_of_normal (T.subtype le_sup_right))
  have hzero : (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (L : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ hQT).trans
      (source_local_sylow_centralizer_eq_bot d hH hB hZ hs hz).le)
  rw [hzero,sup_bot_eq] at hsplit
  have hc := congrArg (fun A : Subgroup G => Nat.card A) hsplit
  simpa only [pCoreIn,card_map_of_injective (L ⊔ (T : Subgroup G)).subtype_injective,
    card_map_of_injective L.subtype_injective,hb.blockU_card] using hc

/-- The original full S₅ action gives the Sylow order if L is an A₅ block. -/
theorem block_sylow_card
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    (hb : ChapterC.IsAlternatingBlock L 5) : Nat.card T = 128 := by
  let K := L ⊔ (T : Subgroup G)
  let S := T.subtype (show (T : Subgroup G) ≤ K from le_sup_right)
  let e := QuotientGroup.quotientKerEquivOfSurjective d.localActor
    (localActor_surjective_of_omega_movement d hH hZ)
  have hquot : Nat.card (K ⧸ pCore 2 K) = 120 := by
    rw [← d.localActor_kernel_eq_core d.normalizes_L,Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hK : Nat.card K = 1920 := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 K),hquot,
      block_local_core_card d hH hB hZ hs hz hb]
  have hS : Nat.card S = 128 := by
    rw [S.card_eq_multiplicity,hK]
    decide +kernel
  exact (Nat.card_congr (subgroupOfEquivOfLe (show (T : Subgroup G) ≤ K from le_sup_right)).toEquiv).symm.trans hS

/-- Compare the same Sylow in the original paired outside quotient. -/
theorem block_outside_core_card
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    (hb : ChapterC.IsAlternatingBlock L 5) : Nat.card (pCore 2 H) = 16 := by
  let S := T.subtype hH.1.1.2
  let q := QuotientGroup.mk' (pCore 2 H)
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  obtain ⟨eQ⟩ := (source_centerfree_residual_core_quotient_models d hH hB hZ hs hz).1
  have hQ : Nat.card (H ⧸ pCore 2 H) = 72 := by
    rw [Nat.card_congr eQ.toEquiv,RegularWreathProduct.card]
    obtain ⟨e3⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    rw [Nat.card_congr e3.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hi : P.index = S.index := S.index_map_of_two_kernel q
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
  have hindex := (P : Subgroup (H ⧸ pCore 2 H)).index_mul_card
  rw [P.card_eq_multiplicity,hQ,hi,
    show (Nat.factorization 72) 2 = 3 from by decide +kernel] at hindex
  have hS : Nat.card S = 128 :=
    (Nat.card_congr (subgroupOfEquivOfLe hH.1.1.2).toEquiv).trans
      (block_sylow_card d hH hB hZ hs hz hb)
  have hSH := (S : Subgroup H).index_mul_card
  rw [hS] at hSH
  have htotal := card_eq_card_quotient_mul_card_subgroup (pCore 2 H)
  rw [hQ] at htotal
  omega


/-- The two natural supports fill the entire outside core forced by an A₅ block. -/
theorem block_outside_core_eq_omega
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    (hb : ChapterC.IsAlternatingBlock L 5) :
    pCore 2 H = (omegaOrbit T H).subgroupOf H := by
  let U := (omegaOrbit T H).subgroupOf H
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  obtain ⟨c,hc,_⟩ := source_solvable_paired_factors d hH hB hZ hs hz
  let W := subspaceCommutator ρ ⊤ (offenderSubgroup ρ)
  have hW : Nat.card W = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      c.toSolvableFFFactors.commutator_finrank,hc]
    norm_num
  have hle : 16 ≤ Nat.card U := by
    rw [←hW]
    exact Nat.card_le_card_of_injective W.subtype W.subtype_injective
  exact (eq_of_le_of_card_ge hU.le_pCore (by
    rw [block_outside_core_card d hH hB hZ hs hz hb]
    exact hle)).symm

/-- If the original omega orbit is the whole outside two-core, each literal
factor preimage produces an A₃-block residual on the original point group. -/
theorem original_paired_point_residual_block_of_omega_core
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hcore : pCore 2 H = (omegaOrbit T H).subgroupOf H)
    {P₁ : Subgroup G} (hOriginal : IsOriginalPairedPointGroup d hH P₁) :
    ChapterC.IsAlternatingBlock (pResidual 2 P₁) 3 := by
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
  have hBq := (ChapterE.ThompsonAction.solvable_pair_images_of_factors S hp U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    hU.quotient_pCore_eq_bot (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S))
    hj c hc ht).2
  have hBm : (ChapterB.baumann (S : Subgroup H)).map H.subtype = B := by
    dsimp only [B,ChapterB.baumann,ChapterB.thompsonAlpha]
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
    rw [hP]
    let J := F ⊔ B
    let : (F.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
      (sup_le F.le_normalizer hBF)
    have hh := pResidual_of_normal_pGroup_supplement 2 (F.subgroupOf J) (B.subgroupOf J)
      (T.isPGroup'.to_le (show B ≤ T from inf_le_left)).comap_subtype
      (by rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self])
    have hm := congrArg (map J.subtype) hh
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le le_sup_left] at hm
    exact hm.symm.trans (map_embedded_pResidual 2 A H.subtype).symm
  let f := H.subtype.comp A.subtype
  let e : pResidual 2 P₁ ≃* pResidual 2 A :=
    ((pResidual 2 P₁).equivMapOfInjective P₁.subtype P₁.subtype_injective).trans
      ((MulEquiv.subgroupCongr (hR.trans (map_map _ _ _))).trans
        ((pResidual 2 A).equivMapOfInjective f
          (H.subtype_injective.comp A.subtype_injective)).symm)
  have hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
      (d.hypothesis.qtke.evenCharacteristic T) hH.1.1)
  have hk : q.ker = U := (QuotientGroup.ker_mk' C).trans
    ((source_omega_centralizer_eq_twoCore d hH hB hZ hs).trans hcore)
  have hb := ChapterC.RankOne.Solvable.factor_preimage_residual_alternatingThree U q (QuotientGroup.mk'_surjective C)
    (QuotientGroup.ker_mk' C) hcore hk hself D i
  exact ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv e.symm hb

/-- Source 13.2.11(5): the original local component cannot be an A₅ block.
Its core split would force the original first point residual to be an A₃ block,
contradicting the independent 13.2.11(6) argument. -/
theorem local_nonblock_of_centerfree_outside
    (hn : ∀ K ∈ MainForward.faithfulLocalComponents T,
      (T : Subgroup G) ≤ normalizer (K : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    ¬ ChapterC.IsAlternatingBlock L 5 := by
  intro hb
  obtain ⟨P₁,hOriginal,_⟩ := exists_paired_point_group d hH hB hZ hs hz
  exact original_paired_point_residual_nonblock d hn hH hB hZ hs hz hOriginal
    (original_paired_point_residual_block_of_omega_core d hH hB hZ hs
      (block_outside_core_eq_omega d hH hB hZ hs hz hb) hOriginal)

/-- The same nonblock conclusion on the literal contrary Borel join used
in source 13.2.12. -/
theorem coreFree_borel_join_local_nonblock
    (hn : ∀ K ∈ MainForward.faithfulLocalComponents T,
      (T : Subgroup G) ≤ normalizer (K : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H)
    (hcore : (H ⊔ borelResidual T L).pCoreIn 2 = ⊥) :
    ¬ ChapterC.IsAlternatingBlock L 5 :=
  local_nonblock_of_centerfree_outside d hn hH hB hZ hs
    (center_eq_bot_of_borel_join_core_eq_bot d hH hZ hcore)

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
