module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryMarkedParabolic
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# The full binary-three quotient of the original escaping group

The original cubic residual makes the local base a rank-one parabolic in
SL₃(2). A graph automorphism exchanges its two nodes, so the actual Sylow
acts internally on the component quotient. The exact conjugation kernel
then gives H = K O₂(H), and the original odd-index local base places this
kernel inside Q. Consequently H = KQ.

The component's specified quotient extends to a surjection H → SL₃(2)
with kernel exactly O₂(H), agreeing on every component element with its
original quotient map. The original radical has image of order four and
is its full inverse image. Its index is 42, and the local base has index
seven. No abelianness or module structure for the whole two-core is inferred.
The full star centralizer is also exactly the join's two-core. The
recognized moved module embeds before any central quotient into the center
of [O₂(H),K], giving its order at least 64. The Chapter12 companion supplies
all inputs on the literal original chosen module.

Source: Aschbacher--Smith, the surviving binary-three case after 7.7.10,
printed p.709, and C.1.31--34, pp.135--137, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThreeQuotient
open BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
variable {G : Type*} [Group G] [Finite G]

/-- The original cubic base is a rank-one parabolic in the binary-three
quotient, and every original Sylow element acts internally. -/
theorem three_flag_inner
    (K A : Subgroup G) [K.Normal] (P : Sylow 2 G)
    (hPA : (P : Subgroup G) ≤ normalizer (A : Set G))
    (hc : Nat.card (A ⧸ pCore 2 A) = 3) (hAK : A ≤ K)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,ZMod 2)) :
    ∃ (hnK : (P : Subgroup G) ≤ normalizer (K : Set G)) (b : Basis 2) (i : Fin 2),
      ((P : Subgroup G).subgroupOf K).map (coreFlagMap K e) = cutStabilizer b Set.univ ∧
      ((A ⊔ (P : Subgroup G)).subgroupOf K).map (coreFlagMap K e) = minimalParabolic b i ∧
      (A ⊔ (P : Subgroup G)).subgroupOf K = (minimalParabolic b i).comap (coreFlagMap K e) ∧
      ∀ p : (P : Subgroup G), coreFlagAction K (P : Subgroup G) hnK e p ∈
        MulAut.innerSubgroup _ := by
  let q := coreFlagMap K e
  have hq := coreFlagMap_surjective K e
  have hk : IsPGroup 2 q.ker := by rw [coreFlagMap_ker]; exact pCore_isPGroup
  have hnK : (P : Subgroup G) ≤ normalizer (K : Set G) := by simp [normalizer_eq_top]
  let α := coreFlagAction K (P : Subgroup G) hnK e
  have heq := coreFlagAction_equivariant K (P : Subgroup G) hnK e
  obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_normal K
  let B := A ⊔ (P : Subgroup G)
  have hSB : (S : Subgroup K) ≤ B.subgroupOf K := by
    rw [hS]
    exact subgroupOf_mono K le_sup_right
  let S' := S.mapSurjective hq
  obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer S'
  have hindex : (S : Subgroup K).relIndex (B.subgroupOf K) = 3 := by
    rw [hS,normal_intersection_relIndex (P : Subgroup G) B K le_sup_right
      (sup_le (hAK.trans le_sup_left) le_sup_right)]
    exact DoubledBinaryMarkedParabolic.local_base_index P A hPA hc
  obtain ⟨i,hi,hpre⟩ := DoubledBinaryMarkedParabolic.flag_node_of_index_three
    q hq hk S (B.subgroupOf K) hSB hindex b hb
  refine ⟨hnK,b,i,hS ▸ hb,hi,hpre,?_⟩
  intro p
  by_contra hp
  have hPN : (P : Subgroup G) ≤ normalizer (B : Set G) :=
    (show (P : Subgroup G) ≤ B from le_sup_right).trans B.le_normalizer
  have hinv := EquivariantLift.map_invariant K q hnK α heq hPN p
  rw [hi] at hinv
  have hh := outer_preserves_minimalParabolic_middle (by decide) (by decide) b i (α p) hp hinv
  omega

omit [Finite G] in
/-- Internal Sylow action makes the original group the component times its
full two-core; no splitting or abelianness of that core is used. -/
theorem group_eq_component_sup_core
    (K : Subgroup G) [K.Normal] (P : Sylow 2 G)
    (hgen : K ⊔ (P : Subgroup G) = ⊤)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,ZMod 2))
    (hnK : (P : Subgroup G) ≤ normalizer (K : Set G))
    (hin : ∀ p : (P : Subgroup G), coreFlagAction K (P : Subgroup G) hnK e p ∈
      MulAut.innerSubgroup _) : K ⊔ pCore 2 G = ⊤ := by
  let J := K ⊔ (P : Subgroup G)
  let d : J ≃* G := (MulEquiv.subgroupCongr hgen).trans topEquiv
  let α := (pCoreJoinAction 2 hnK).comp d.symm.toMonoidHom
  have hc : center (K ⧸ pCore 2 K) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hz := (centerCongr e ⟨x,hx⟩).property
    exact e.map_eq_one_iff.mp (Matrix.PSL3Two.center_eq_bot.le hz)
  have hk : α.ker = pCore 2 G := by
    change ((pCoreJoinAction 2 hnK).ker).comap d.symm.toMonoidHom = _
    rw [pCoreJoinAction_kernel 2 hnK P.isPGroup' hc,←pCore_map_iso 2 d.symm,
      comap_map_eq_self_of_injective d.symm.injective]
  have hinner (p : (P : Subgroup G)) : α p ∈ MulAut.innerSubgroup _ := by
    have hp := hin p
    rw [←MulAut.map_innerSubgroup_congr (e.trans (slEquivLinear 3))] at hp
    obtain ⟨a,ha,he⟩ := hp
    have he' : (MulAut.congr (e.trans (slEquivLinear 3))) a =
        (MulAut.congr (e.trans (slEquivLinear 3))) (α p) := he
    exact (MulAut.congr (e.trans (slEquivLinear 3))).injective he' ▸ ha
  have hcomp (k : K) : α k = MulAut.conj (QuotientGroup.mk' (pCore 2 K) k) := by
    exact pCoreJoinAction_on_component 2 hnK k
  have hP : (P : Subgroup G) ≤ K ⊔ pCore 2 G := by
    intro p hp
    obtain ⟨x,hx⟩ := hinner ⟨p,hp⟩
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) x
    have he : α k = α p := (hcomp k).trans hx
    have hd : (k : G)⁻¹ * p ∈ pCore 2 G := by
      rw [←hk]
      change α ((k : G)⁻¹ * p) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    have hh := (K ⊔ pCore 2 G).mul_mem (mem_sup_left k.property) (mem_sup_right hd)
    simpa only [mul_inv_cancel_left] using hh
  exact top_unique (hgen ▸ sup_le le_sup_left hP)

/-- The component's specified quotient extends to the whole original group,
with exactly the full ambient two-core as kernel. -/
theorem full_quotient_map
    (K : Subgroup G) [K.Normal] (hgen : K ⊔ pCore 2 G = ⊤)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,ZMod 2)) :
    ∃ q : G →* SL(3,ZMod 2), Function.Surjective q ∧ q.ker = pCore 2 G ∧
      ∀ k : K, q k = e (QuotientGroup.mk' (pCore 2 K) k) := by
  let π := QuotientGroup.mk' (pCore 2 G)
  let f := π.comp K.subtype
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp,K.range_subtype]
    have hh := congrArg (map π) hgen
    rw [Subgroup.map_sup,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    have hz : (pCore 2 G).map π = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      rw [QuotientGroup.ker_mk']
    simpa only [hz,sup_bot_eq] using hh
  have hk : f.ker = pCore 2 K := by
    change (π.ker).comap K.subtype = _
    rw [QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 (inferInstance : K.Normal).isSubnormal).symm
  let d : (K ⧸ pCore 2 K) ≃* (G ⧸ pCore 2 G) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  let q := (d.symm.trans e).toMonoidHom.comp π
  refine ⟨q,(d.symm.trans e).surjective.comp (QuotientGroup.mk'_surjective _),?_,?_⟩
  · rw [MonoidHom.ker_comp_of_injective _ _ (d.symm.trans e).injective,QuotientGroup.ker_mk']
  · intro k
    have hd : d (QuotientGroup.mk' (pCore 2 K) k) = π k := rfl
    change e (d.symm (π k)) = _
    rw [←hd,d.symm_apply_apply]

/-- The original index-two radical maps to a subgroup of order four in the full binary
three quotient. Its inverse image contains the entire ambient two-core. -/
theorem radical_image_card
    (q : G →* SL(3,ZMod 2)) (hq : Function.Surjective q) (hk : q.ker = pCore 2 G)
    (P : Sylow 2 G) (Q : Subgroup G) (hQ : pCore 2 G ≤ Q)
    (hQP : Q ≤ (P : Subgroup G)) (hindex : Q.relIndex (P : Subgroup G) = 2) :
    Nat.card (Q.map q) = 4 ∧ (Q.map q).comap q = Q := by
  let S := P.mapSurjective hq
  have hc : Nat.card S = 8 := by
    rw [S.card_eq_multiplicity,Matrix.PSL3Two.card_SL]
    norm_num [Nat.factorization]
    rw [show 168 = 2^3*21 from rfl,padicValNat.mul (by decide) (by decide),
      padicValNat.pow,padicValNat_self,
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 21)]
    rfl
  have hi : (Q.map q).relIndex (S : Subgroup _) = 2 := by
    change (Q.map q).relIndex ((P : Subgroup G).map q) = 2
    rw [relIndex_map_map,sup_eq_left.mpr (hk ▸ hQ),
      sup_eq_left.mpr (hk ▸ hQ.trans hQP)]
    exact hindex
  have hh := relIndex_mul_relIndex (⊥ : Subgroup SL(3,ZMod 2)) (Q.map q)
    (S : Subgroup _) bot_le (map_mono (f := q) hQP)
  rw [relIndex_bot_left,relIndex_bot_left,hi,hc] at hh
  exact ⟨by omega,comap_map_eq_self (hk ▸ hQ)⟩

/-- Full binary-three recognition up to the shape of the two-core. Both
original quotient maps and the original cubic base are retained. -/
@[expose] def Conclusion (K A Q R : Subgroup G) : Prop :=
  ∃ e : (K ⧸ pCore 2 K) ≃* SL(3,ZMod 2),
    ∃ (hn : R ≤ normalizer (K : Set G)) (b : Basis 2) (i : Fin 2),
      (R.subgroupOf K).map (coreFlagMap K e) = cutStabilizer b Set.univ ∧
      ((A ⊔ R).subgroupOf K).map (coreFlagMap K e) = minimalParabolic b i ∧
      (A ⊔ R).subgroupOf K = (minimalParabolic b i).comap (coreFlagMap K e) ∧
      (∀ r : R, coreFlagAction K R hn e r ∈ MulAut.innerSubgroup _) ∧
      K ⊔ pCore 2 G = ⊤ ∧ K ⊔ Q = ⊤ ∧
      ∃ q : G →* SL(3,ZMod 2), Function.Surjective q ∧ q.ker = pCore 2 G ∧
        (∀ k : K, q k = e (QuotientGroup.mk' (pCore 2 K) k)) ∧
        Nat.card (Q.map q) = 4 ∧ (Q.map q).comap q = Q ∧
        Q.index = 42 ∧ (A ⊔ R).index = 7

/-- Apply the marked-node calculation to the literal original Sylow and
index-two radical. No whole-core classification premise is required. -/
theorem conclusion_of_cubic_base
    (K A Q : Subgroup G) [K.Normal] (P : Sylow 2 G)
    (hPA : (P : Subgroup G) ≤ normalizer (A : Set G))
    (hc : Nat.card (A ⧸ pCore 2 A) = 3) (hAK : A ≤ K)
    (hgen : K ⊔ (P : Subgroup G) = ⊤)
    (hQ : pCore 2 G ≤ Q) (hQP : Q ≤ (P : Subgroup G))
    (hindex : Q.relIndex (P : Subgroup G) = 2)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,ZMod 2)) : Conclusion K A Q (P : Subgroup G) := by
  obtain ⟨hn,b,i,hS,hB,hpre,hin⟩ := three_flag_inner K A P hPA hc hAK e
  have hcore := group_eq_component_sup_core K P hgen e hn hin
  have hjoin : K ⊔ Q = ⊤ := top_unique (hcore ▸ sup_le_sup_left hQ K)
  obtain ⟨q,hq,hk,heq⟩ := full_quotient_map K hcore e
  obtain ⟨hcard,hfull⟩ := radical_image_card q hq hk P Q hQ hQP hindex
  have hcount := (Q.map q).index_mul_card
  rw [Q.index_map_eq hq (hk ▸ hQ),hcard,Matrix.PSL3Two.card_SL] at hcount
  have hiQ : Q.index = 42 := by omega
  have hiP := relIndex_mul_index hQP
  rw [hindex,hiQ] at hiP
  have hiB := relIndex_mul_index (show (P : Subgroup G) ≤ A ⊔ (P : Subgroup G) from le_sup_right)
  rw [DoubledBinaryMarkedParabolic.local_base_index P A hPA hc] at hiB
  have hbase : (A ⊔ (P : Subgroup G)).index = 7 := by omega
  exact ⟨e,hn,b,i,hS,hB,hpre,hin,hcore,hjoin,q,hq,hk,heq,hcard,hfull,hiQ,hbase⟩

open Representation Representation.BinaryOffender
open ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open scoped IsMulCommutative

/-- The recognized two-copy moved space is an actual order-64 subgroup
of the center of the whole commutator core, before any central quotient. -/
theorem moved_center_card
    {K Q : Subgroup G} {J : Subgroup (StarQuotient K Q)}
    (hKJ : starImage K Q K ≤ J)
    (s : MovedSection ((starRepresentation K Q).comp J.subtype)
      ((starImage K Q K).subgroupOf J))
    (F : BinaryField) (hF : F.degree = 1)
    (hm : IsRepeatedLinearNatural (s.space.toRepresentation.comp
      ((starImage K Q K).subgroupOf J).subtype) F 3 2) :
    64 ≤ Nat.card (center ((⁅(K ⊔ Q).pCoreIn 2,K⁆ : Subgroup G))) := by
  let U := starV K Q
  let C := K.subgroupOf (K ⊔ Q)
  let Z := ⁅U,C⁆
  let D := ⁅pCore 2 (K ⊔ Q : Subgroup G),C⁆
  have hU : U ≤ pCore 2 (K ⊔ Q : Subgroup G) := by
    intro u hu
    exact ((Stellmacher.mem_omegaOneCenterAmbient_iff _ u).mp hu).1
  have hZD : Z ≤ D := commutator_mono hU le_rfl
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_injective
    (inclusion (commutator_le_left U C)) (inclusion_injective _)
  let q := QuotientGroup.mk' (starKernel K Q)
  have hs : s.space.toSubmodule = subspaceCommutator (starRepresentation K Q) ⊤ (C.map q) := by
    rw [s.space_eq]
    change subspaceCommutator ((starRepresentation K Q).comp J.subtype) ⊤
      ((starImage K Q K).subgroupOf J) = _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hKJ]
    rfl
  let d := (NormalElementaryQuotient.movedEquiv U q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) C).trans (LinearEquiv.ofEq _ _ hs.symm)
  obtain ⟨a⟩ := hm
  have hc : Nat.card Z = 64 := by
    change Nat.card (Additive Z) = _
    rw [Nat.card_congr (d.trans a.linearEquiv).toEquiv]
    rw [Nat.card_fun,Nat.card_fun,Nat.card_fin,Nat.card_fin,F.card_eq,hF]
    norm_num
  let f : Z →* center D := {
    toFun z := ⟨⟨z,hZD z.property⟩,by
      apply mem_center_iff.mpr
      intro x
      apply Subtype.ext
      exact (core_le_starKernel K Q (commutator_le_left _ _ x.property)
        z (commutator_le_left U C z.property)).symm⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : center D => (z.val : (K ⊔ Q : Subgroup G))) he)
  have hd : D.map (K ⊔ Q : Subgroup G).subtype = (⁅(K ⊔ Q).pCoreIn 2,K⁆ : Subgroup G) := by
    rw [map_commutator,map_subgroupOf_eq_of_le (show K ≤ K ⊔ Q from le_sup_left)]
    rfl
  let e : D ≃* (⁅(K ⊔ Q).pCoreIn 2,K⁆ : Subgroup G) :=
    (D.equivMapOfInjective (K ⊔ Q : Subgroup G).subtype
      (K ⊔ Q : Subgroup G).subtype_injective).trans (MulEquiv.subgroupCongr hd)
  have hb := Nat.card_le_card_of_injective f hf
  rw [hc,Nat.card_congr (centerCongr e).toEquiv] at hb
  exact hb

omit [Finite G] in
/-- Centerlessness identifies the full original star kernel with the
whole join's two-core, retaining its literal centralizer definition. -/
theorem star_kernel_eq_twoCore
    {K Q : Subgroup G} (hN : Q ≤ normalizer (K : Set G)) (hQ : IsPGroup 2 Q)
    (hker : KernelConclusion K Q)
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    starKernel K Q = pCore 2 (K ⊔ Q : Subgroup G) := by
  have hc : center (K ⧸ pCore 2 K) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hz := (centerCongr e ⟨x,hx⟩).property
    exact e.map_eq_one_iff.mp (Matrix.PSL3Two.center_eq_bot.le hz)
  exact le_antisymm
    ((starKernel_le_coreActionKernel hN hker.upper).trans_eq
      (pCoreJoinAction_kernel 2 hN hQ hc)) hker.lower

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThreeQuotient
