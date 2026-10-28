module
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
public import Theory.GroupTheory.CComponent.A5PairSylowMaximal
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import CFSG.Quasithin.Chapter10.SourceA5MinimalParabolic
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.Contracts
/-!
# The original rank-one minimal parabolic

Borel uniqueness in SL₂ gives a unique maximal overgroup of each factor
Sylow subgroup. The two original components form a simple pair modulo the
local two-core, and a Sylow element exchanges them. Pair uniqueness lifts
through the two-core to the literal local join. Its Sylow subgroup is not
normal, as its image in SL₂ is nontrivial, proper and not normal.
This generalizes the paired A₅ proof to the field in RankOneNatural.
Source: Aschbacher--Smith, 10.1.2(6), printed p.742.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G]
  {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem two_dvd_sl_card : 2 ∣ Nat.card SL(2,F) := by
  let := Fintype.ofFinite F
  obtain ⟨n, _, hn⟩ := FiniteField.card F 2
  have h2 : 2 ∣ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self 2 n.ne_zero
  rw [← Matrix.SpecialLinearGroup.card_upperUnipotent F] at h2
  exact h2.trans (card_subgroup_dvd_card (Matrix.SpecialLinearGroup.upperUnipotent F))

variable [hsimple : IsSimpleGroup SL(2,F)]
omit hsimple in
private theorem rank_one_sylow_intersection (S : Sylow 2 G) (A : Subgroup G)
    (hs : A.IsSubnormal) (e : A ≃* SL(2,F)) :
    Order.HasUniqueMaximalOver (A ⊓ (S : Subgroup G)) A ∧ A ⊓ (S : Subgroup G) ≠ ⊥ := by
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_subnormal A hs
  have hu : Order.HasUniqueMaximalOver (P : Subgroup A) ⊤ :=
    hasUniqueMaximalOver_of_surjective e.toMonoidHom e.surjective
      (by rw [e.toMonoidHom.ker_eq_bot e.injective]; exact bot_le)
      (Matrix.SpecialLinearGroup.sylow_hasUniqueMaximalOver 2 (P.mapSurjective e.surjective))
  have hum := hasUniqueMaximalOver_map_subtype hu
  rw [hP, subgroupOf_map_subtype, inf_comm] at hum
  refine ⟨hum, ?_⟩
  have hd : 2 ∣ Nat.card A := by
    rw [Nat.card_congr e.toEquiv]
    exact two_dvd_sl_card
  intro he
  apply P.ne_bot_of_dvd_card hd
  apply (map_eq_bot_iff_of_injective _ A.subtype_injective).mp
  rw [hP, subgroupOf_map_subtype, inf_comm]
  exact he

omit [Finite G] in
private theorem simple_pair_disjoint (A B : Subgroup G) [IsSimpleGroup A]
    [Group.IsPerfect A] (hc : B ≤ centralizer (A : Set G)) : Disjoint A B := by
  have hz : center A = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center A) inferInstance with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp h)).elim
  apply disjoint_def.mpr
  intro x hxA hxB
  have hx : (⟨x,hxA⟩ : A) ∈ center A := mem_center_iff.mpr fun a =>
    Subtype.ext (hc hxB a a.property)
  have he : (⟨x,hxA⟩ : A) = 1 := mem_bot.mp (hz ▸ hx)
  exact congrArg Subtype.val he

include hsimple in
private theorem rank_one_simple_pair_unique (S : Sylow 2 G) (A : Subgroup G)
    (hA : A.IsCComponent) (e : A ≃* SL(2,F))
    (hi : (normalizer (A : Set G)).index = 2)
    (hgen : A ⊔ (S : Subgroup G) = ⊤) :
    Order.HasUniqueMaximalOver (S : Subgroup G) ⊤ := by
  have hs : ¬ (S : Subgroup G) ≤ normalizer (A : Set G) := by
    intro hs
    have hd := index_dvd_of_le hs
    rw [hi] at hd
    exact S.not_dvd_index hd
  obtain ⟨s,hs,hsn⟩ := Set.not_subset.mp hs
  let B := A.map (MulAut.conj s).toMonoidHom
  have hm : B ≠ A := fun he => hsn (mem_normalizer_iff_map_conj_eq.mpr he)
  have hB : B.IsCComponent := hA.map_equiv (MulAut.conj s)
  let eB : B ≃* SL(2,F) := ((MulAut.conj s).subgroupMap A).symm.trans e
  let : IsSimpleGroup A := e.isSimpleGroup
  let : IsSimpleGroup B := eB.isSimpleGroup
  let := hA.perfect
  have hc : B ≤ centralizer (A : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (by
      rw [commutator_comm]
      exact simple_subnormal_commute_of_ne A B hA.subnormal hB.subnormal hm.symm)
  have hd := simple_pair_disjoint A B hc
  obtain ⟨huA,hneA⟩ := rank_one_sylow_intersection S A hA.subnormal e
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_subnormal A hA.subnormal
  have hu := hasUniqueMaximalOver_of_simple_pair_sylow A B (S : Subgroup G)
    hc hd huA hneA S.isPGroup' P hP
    (fun g _ => NormPair.conjugate_eq_or_eq_of_normalizer_index_two hi hm g) s hs rfl
  have htop : (A ⊔ B) ⊔ (S : Subgroup G) = ⊤ :=
    top_unique (hgen ▸ sup_le_sup (le_sup_left : A ≤ A ⊔ B) le_rfl)
  rwa [htop] at hu

include hsimple in
/-- A paired rank-one C-component supplies unique maximality over the original Sylow. -/
private theorem rank_one_pair_sylow_unique
    (S : Sylow 2 G) (A : Subgroup G) (hA : A.IsCComponent)
    (e : (A ⧸ pCore 2 A) ≃* SL(2,F))
    (hi : (normalizer (A : Set G)).index = 2)
    (hgen : A ⊔ (S : Subgroup G) = ⊤) :
    Order.HasUniqueMaximalOver (S : Subgroup G) ⊤ := by
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  let q := QuotientGroup.mk' (pCore 2 G)
  let Abar := A.map q
  let Sbar := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hAb : Abar.IsCComponent := hA.map_quotient (pCore 2 G)
  let eb : Abar ≃* SL(2,F) := (cComponentTwoCoreQuotientEquiv hA).symm.trans e
  have hib : (normalizer (Abar : Set (G ⧸ pCore 2 G))).index = 2 :=
    (cComponent_normalizer_index_quotient hA (pCore 2 G)).trans hi
  have hgenb : Abar ⊔ (Sbar : Subgroup (G ⧸ pCore 2 G)) = ⊤ := by
    change A.map q ⊔ (S : Subgroup G).map q = ⊤
    rw [← Subgroup.map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  exact hasUniqueMaximalOver_of_surjective q (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal S)
    (rank_one_simple_pair_unique Sbar Abar hAb eb hib hgenb)

include hsimple in
private theorem rank_one_sylow_not_normal
    (S : Sylow 2 G) (A : Subgroup G) (hA : A.IsCComponent)
    (e : (A ⧸ pCore 2 A) ≃* SL(2,F)) :
    ¬ (S : Subgroup G).Normal := by
  intro hn
  let := hn
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_subnormal A hA.subnormal
  let : (P : Subgroup A).Normal := by rw [hP]; infer_instance
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q := P.mapSurjective hf
  have hQ : (Q : Subgroup SL(2,F)).Normal :=
    (inferInstance : (P : Subgroup A).Normal).map f hf
  rcases hQ.eq_bot_or_eq_top with hz | hz
  · exact Q.ne_bot_of_dvd_card two_dvd_sl_card hz
  · exact (Matrix.SpecialLinearGroup.sylow_hasUniqueMaximalOver 2 Q).1.ne hz

variable {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
include D e

omit [Finite F] [CharP F 2] hsimple in
private theorem rank_one_internal :
    (L.subgroupOf (localJoin T L)).IsCComponent ∧
    Nonempty (((L.subgroupOf (localJoin T L)) ⧸ pCore 2 (L.subgroupOf (localJoin T L)))
      ≃* SL(2,F)) ∧
    L.subgroupOf (localJoin T L) ⊔
      ((T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right) :
        Sylow 2 (localJoin T L)) : Subgroup (localJoin T L)) = ⊤ := by
  let H := localJoin T L
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  have hA : (L.subgroupOf H).IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  let a := subgroupOfEquivOfLe hLH
  let b := a.toMonoidHom.pCoreQuotientEquiv (p := 2) a.surjective
    (by rw [a.toMonoidHom.ker_eq_bot a.injective]; exact IsPGroup.of_bot)
  refine ⟨hA, ⟨b.trans e⟩, ?_⟩
  change L.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
  rw [← subgroupOf_sup hLH (show (T : Subgroup G) ≤ H from le_sup_right)]
  have hh : L ⊔ (T : Subgroup G) = H := (componentOrbit_sup L (T : Subgroup G)).symm
  rw [hh, subgroupOf_self]

omit e in
private theorem rank_one_nonnormal_index
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (normalizer (L.subgroupOf (localJoin T L) : Set (localJoin T L))).index = 2 := by
  have hi := source_nonnormal_normalizer_index D.simpleQTKE D.maximal.1 hn
  change (normalizer (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔
    (T : Subgroup G)) : Set (componentOrbit L (T : Subgroup G) ⊔
    (T : Subgroup G) : Subgroup G))).index = 2
  rw [componentOrbit_sup]
  exact hi

include hsimple in
/-- The original rank-one branch is a minimal parabolic on its actual join. -/
theorem minimal_parabolic
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ChapterB.IsMinimalParabolicOver (T.subtype (show (T : Subgroup G) ≤
      localJoin T L from le_sup_right)) ⊤ := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let A := L.subgroupOf H
  obtain ⟨hA, ⟨eA⟩, hgen⟩ := rank_one_internal D e
  have hu := rank_one_pair_sylow_unique S A hA eA (rank_one_nonnormal_index D hn) hgen
  apply (ChapterB.isMinimalParabolicOver_top_iff S).mpr
  obtain ⟨B,hB,huniq⟩ := hu.2
  exact ⟨⟨B,⟨hB.2.isCoatom,hB.1⟩,fun K hK => huniq K ⟨hK.2,hK.1.covBy_top⟩⟩,
    rank_one_sylow_not_normal S A hA eA⟩

omit e hsimple in
theorem minimal_parabolic_of_rankOneNatural
    (hmodel : RankOneNatural D)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ChapterB.IsMinimalParabolicOver (T.subtype (show (T : Subgroup G) ≤
      localJoin T L from le_sup_right)) ⊤ := by
  obtain ⟨n,hnn,e,_⟩ := hmodel
  let : NeZero n := ⟨by omega⟩
  have hF : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n (by omega)]
    exact (show 2^2 ≤ 2^n from Nat.pow_le_pow_right (by decide) (by omega))
  let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := GaloisField 2 n) hF
  let : IsSimpleGroup SL(2,GaloisField 2 n) :=
    (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 n)).isSimpleGroup
  exact minimal_parabolic D e hn

end CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
