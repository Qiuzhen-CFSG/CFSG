module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.IntrinsicSeedGeometry

/-!
# The common critical center in the full beta two-core

A normal elementary subgroup of each actual local Sylow lies in its omega
center. For the exceptional order-144 quotient, its normal elementary nine
gives a faithful Sylow embedding in GL₂(3). The explicit semidihedral
presentation makes the normal elementary subgroup central. The other rows
use the proved rank-one Sylow calculation.

The image of Z_alpha intersect Z_gamma is therefore central in the alpha
edge Sylow. If nontrivial, intrinsic Sylow uniqueness identifies the two
edge Sylows and hence the two neighbors. Thus the common center lies in
Q_beta, including the strict enlargement and without either catalogue.
IntrinsicPairQuotient applies this to the literal source two-seed quotient.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.2)--(11.3)(a), pp.168--169; the exceptional calculation uses the
semidihedral Sylow presentation in Alperin--Brauer--Gorenstein II.2,
Lemma 1, via Theory.SpecificGroups.GL2.SemidihedralSylow.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open Reduction Representation.AffineNine
private theorem normal_elementary_central_of_embedding
    {H : Type*} [Group H] [Finite H] (hH : Nat.card H = 16)
    (f : H →* GL (Fin 2) (ZMod 3)) (hf : Function.Injective f)
    (E : Subgroup H) [E.Normal] [IsElementaryAbelian 2 E] : E ≤ center H := by
  let U := f.range
  have hU : Nat.card U = 16 := (Nat.card_congr (MonoidHom.ofInjective hf).symm.toEquiv).trans hH
  have hp : IsPGroup 2 U := IsPGroup.of_card (p := 2) (n := 4) hU
  have hGL : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ,ZMod.card]
  have hi : U.index = 3 := by
    have hc := U.card_mul_index
    rw [hU,hGL] at hc
    omega
  let T := hp.toSylow (by rw [hi]; decide)
  obtain ⟨S,n,hn,hS,a,b,ha,hb,hc,hg,hcenter,_⟩ :=
    Matrix.GeneralLinearGroup.exists_semidihedral_sylow (ZMod 3) (by norm_num [Nat.card_zmod])
  have hSc : Nat.card S = 16 := by
    rw [S.card_eq_multiplicity,hGL]
    decide +kernel
  have hn4 : n = 4 :=
    (Nat.pow_right_injective (by decide : 1 < 2)) (hS.symm.trans hSc)
  subst n
  norm_num only at ha hc hcenter
  let e : H ≃* S := (MonoidHom.ofInjective hf).trans (T.equiv S)
  let D := E.map e.toMonoidHom
  let : D.Normal := (inferInstance : E.Normal).map e.toMonoidHom e.surjective
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map e.toMonoidHom
  have hD : D ≤ center S := by
    by_cases hz : D = ⊥
    · rw [hz]; exact bot_le
    rw [Semidihedral.normal_elementary_eq_of_order_sixteen a b ha hb hc hg D hz,hcenter]
  intro x hx
  apply mem_center_iff.mpr
  intro y
  apply e.injective
  simpa only [map_mul,MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe] using
    mem_center_iff.mp (hD (mem_map_of_mem e.toMonoidHom hx)) (e y)

private theorem normal_elementary_central_of_nine
    {D : Type*} [Group D] [Finite D] (hD : Nat.card D = 144)
    (N : Subgroup D) [N.Normal] [IsElementaryAbelian 3 N]
    (hN : Nat.card N = 9) (hcore : pCore 2 D = ⊥)
    (S : Sylow 2 D) (E : Subgroup D) [IsElementaryAbelian 2 E]
    (hES : E ≤ S) (hn : (S : Subgroup D) ≤ normalizer (E : Set D)) :
    E ≤ omegaCenterIn (S : Subgroup D) := by
  have hS : Nat.card S = 16 := by
    rw [S.card_eq_multiplicity,hD]
    decide +kernel
  have hNS : N.IsComplement' (S : Subgroup D) := by
    apply isComplement'_of_coprime
    · rw [hN,hS,hD]
    · rw [hN,hS]; decide
  have hc := centralizer_eq_nine_of_twoCore_eq_bot N S S.isPGroup' hNS.sup_eq_top hcore
  let a := (MulAut.conjNormal : D →* MulAut N).comp (S : Subgroup D).subtype
  have ha : Function.Injective a := by
    apply a.ker_eq_bot_iff.mp
    apply (eq_bot_iff_forall _).mpr
    intro s hs
    have hsN : (s : D) ∈ N := by
      rw [←hc,←MulAut.conjNormal_ker_eq_centralizer N]
      exact hs
    exact Subtype.ext (mem_bot.mp (hNS.disjoint.le_bot ⟨hsN,s.property⟩))
  obtain ⟨f,hf⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := 3) (n := 2) N (by rw [hN]; decide)
  let E₀ := E.subgroupOf (S : Subgroup D)
  let : E₀.Normal := normal_subgroupOf_of_le_normalizer hn
  let : IsElementaryAbelian 2 E₀ := IsElementaryAbelian.subgroupOf hES
  have hcent := normal_elementary_central_of_embedding hS (f.comp a) (hf.comp ha) E₀
  intro x hx
  apply (mem_omegaCenterIn_iff _ _).mpr
  refine ⟨hES hx,?_,elemPow_eq_one_of_isElementaryAbelian x hx⟩
  intro y hy
  exact congrArg Subtype.val (mem_center_iff.mp
    (hcent (show (⟨x,hES hx⟩ : S) ∈ E₀ from hx)) ⟨y,hy⟩)

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (Reduction.G₀ L S))
local notation "G₀" => Reduction.G₀ L S

/-- Normal elementary images are central in every actual local Sylow,
including the strict projective enlargement of order 144. -/
theorem reduced_normal_elementary_le_sylow_omega (h : HypothesisF11 L S)
    (v : Vertex F) (T : Sylow 2 (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)))
    (E : Subgroup (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)))
    [IsElementaryAbelian 2 E] (hET : E ≤ T)
    (hn : (T : Subgroup (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v))) ≤
      normalizer (E : Set (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)))) :
    E ≤ omegaCenterIn (T : Subgroup (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v))) := by
  let := finite_endpoints (reduced_triple h)
  let M := graphLocalGroup F v
  let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hs := reduced_graph_rankOne_or_normal_nine h v
  dsimp only [reducedFamily] at hs
  rcases hs with hm | ⟨hc,N,hN,hE,h9⟩
  · exact source_rank_one_elementary_le_sylow_omega hm T E hET
  · let := hN
    let := hE
    exact normal_elementary_central_of_nine hc N h9 (pCore_quotient_pCore_eq_bot 2) T E hET hn

/-- The common center of two different critical neighbors lies in the
actual beta two-core, without either local catalogue. -/
theorem reduced_source_center_intersection_le_beta (h : HypothesisF11 L S)
    {a b c : Vertex F} (hc : IsCriticalPair F a b) (hb : DGS85.b F = 1)
    (hbc : (graph F).Adj b c) (hac : a ≠ c) :
    Z F a ⊓ Z F c ≤ Q F b := by
  let ht := reduced_triple h
  let hB := reduced_borel_core_sylow h
  let d := reducedFullEarlierLocalTheorems h
  let := finite_endpoints ht
  let := source_center_elementary ht a
  have hab := source_critical_one_adjacent hc hb
  let M := graphLocalGroup F b
  let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let q := QuotientGroup.mk' (pCore 2 M)
  obtain ⟨R,hR⟩ := source_edge_core_local_sylow ht hB d hab.symm
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow ht hB d hbc
  change Sylow 2 M at R T
  change (R : Subgroup M).map M.subtype =
    (stabilizer F b ⊓ stabilizer F a).pCoreIn 2 at hR
  change (T : Subgroup M).map M.subtype =
    (stabilizer F b ⊓ stabilizer F c).pCoreIn 2 at hT
  have hZaR : Z F a ≤ (R : Subgroup M).map M.subtype := by
    rw [hR,inf_comm]
    exact ((source_Z_Q_U ht a).1.trans (map_subtype_le _)).trans
      (Noncommuting.graph_Q_le_edgeCore ht hab)
  have hZcT : Z F c ≤ (T : Subgroup M).map M.subtype := by
    rw [hT,inf_comm]
    exact ((source_Z_Q_U ht c).1.trans (map_subtype_le _)).trans
      (Noncommuting.graph_Q_le_edgeCore ht hbc.symm)
  let A := (Z F a).subgroupOf M
  let J := (Z F a ⊓ Z F c).subgroupOf M
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf (hZaR.trans (map_subtype_le _))
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.of_le (show J ≤ A from fun _ hx => hx.1)
  let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
  let : IsElementaryAbelian 2 (J.map q) := IsElementaryAbelian.map q
  have hAR : A ≤ (R : Subgroup M) := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hZaR hx
    exact (Subtype.ext he : y = x) ▸ hy
  have hJT : J ≤ (T : Subgroup M) := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hZcT hx.2
    exact (Subtype.ext he : y = x) ▸ hy
  have hnA : (R : Subgroup M) ≤ normalizer (A : Set M) := by
    intro x hx
    apply le_normalizer_comap M.subtype
    apply stabilizer_normalizes_Z F a
    exact ((pCoreIn_le 2 _).trans inf_le_right) (hR ▸ mem_map_of_mem M.subtype hx)
  let R' := R.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let T' := T.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hJA : J.map q ≤ A.map q := map_mono (show J ≤ A from fun _ hx => hx.1)
  have hcent := reduced_normal_elementary_le_sylow_omega h b R' (A.map q)
    (map_mono hAR) ((map_mono hnA).trans (le_normalizer_map q))
  have hJbot : J.map q = ⊥ := by
    by_contra hne
    have hnJ : (R' : Subgroup (M ⧸ pCore 2 M)) ≤ normalizer (J.map q : Set (M ⧸ pCore 2 M)) := by
      apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      apply le_centralizer_iff.mpr
      intro x hx
      exact ((mem_omegaCenterIn_iff _ _).mp (hcent (hJA hx))).2.1
    have huniq := reduced_graph_normal_elementary_sylow_unique h
    dsimp only [reducedFamily] at huniq
    have he := @huniq b R' T' (J.map q) (inferInstance : IsElementaryAbelian 2 (J.map q))
      (hJA.trans (map_mono hAR)) (map_mono hJT) hnJ hne
    have hRT : R = T := by
      apply Sylow.ext
      have hh := congrArg (fun U : Sylow 2 (M ⧸ pCore 2 M) =>
        (U : Subgroup _).comap q) he
      change ((R : Subgroup M).map q).comap q = ((T : Subgroup M).map q).comap q at hh
      rw [comap_map_eq,comap_map_eq,show q.ker = pCore 2 M from QuotientGroup.ker_mk' _] at hh
      rwa [sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal R),
        sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal T)] at hh
    apply hac
    exact graph_intrinsic_edgeCore_unique_neighbor ht hB hab.symm hbc (by
      rw [←hR,hRT,hT]
      exact (pCoreIn_le 2 _).trans inf_le_right)
  have hk := (Subgroup.map_eq_bot_iff _).mp hJbot
  rw [QuotientGroup.ker_mk'] at hk
  intro x hx
  rw [←localGroup_core_eq F d b]
  exact mem_map_of_mem M.subtype (hk (show (⟨x,(hZaR.trans (map_subtype_le _)) hx.1⟩ : M) ∈ J from hx))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
