module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Normalizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.Quotient
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalBender
public import Theory.GroupTheory.CComponent.A5PairSylowMaximal

/-!
# The half-Sylow normalizer for the original Bender quotient

The actual component and its exchanged conjugate become commuting simple
factors modulo the local two-core. The concrete Bender Borel theorem and
paired-factor maximality prove that the original join is minimal over T.
Common-normal control then bounds the normalizer of the literal N_T(L).
No module coordinates or choice of a classified seed are assumed.

This proves the binary rank-one and Suzuki normalizer branches in 10.2.5.
The linear-three branch remains separate.
Source: Aschbacher--Smith, 10.1.2(6), 10.2.5, pp.742,747--748.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 ChapterF.Source
variable {G : Type*} [Group G] [Finite G]

private theorem bender_sylow_interval (S : Sylow 2 G) (A : Subgroup G)
    (hs : A.IsSubnormal) (hm : ClassificationModels.IsBenderModel A) :
    Order.HasUniqueMaximalOver (A ⊓ (S : Subgroup G)) A ∧
    A ⊓ (S : Subgroup G) ≠ ⊥ ∧
    ∀ P : Subgroup G, A ⊓ (S : Subgroup G) ≤ P → P < A → Group.IsSolvable P := by
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_subnormal A hs
  have hf := ChapterE.Structure.bender_sylow_facts hm R
  have hRm : (R : Subgroup A).map A.subtype = (S : Subgroup G) ⊓ A := by
    rw [hR,subgroupOf_map_subtype]
  have hb := rankOneBorelFacts_of_sylow A (S : Subgroup G) R hRm hf
  have hSB : A ⊓ (S : Subgroup G) ≤ borel A (S : Subgroup G) := by
    change _ ≤ A ⊓ normalizer (((S : Subgroup G) ⊓ A : Subgroup G) : Set G)
    exact le_inf inf_le_left (by simpa only [inf_comm A] using ((S : Subgroup G) ⊓ A).le_normalizer)
  have hc : borel A (S : Subgroup G) ⋖ A := by
    refine ⟨hb.proper,?_⟩
    intro P hBP hPA
    exact hBP.not_ge (hb.unique_maximal P (by simpa only [inf_comm A] using hSB.trans hBP.le) hPA)
  refine ⟨⟨hSB.trans_lt hb.proper, _, ⟨hSB,hc⟩, ?_⟩, ?_, ?_⟩
  · intro P hP
    have hPB := hb.unique_maximal P (by simpa only [inf_comm A] using hP.1) hP.2.lt
    exact ((hP.2.eq_or_eq hPB hb.proper.le).resolve_right hb.proper.ne).symm
  · intro he
    have hRbot : (R : Subgroup A) = ⊥ := by
      apply (map_eq_bot_iff_of_injective _ A.subtype_injective).mp
      rw [hRm,inf_comm,he]
    have h := hf.proper.ne
    change normalizer ((R : Subgroup A) : Set A) ≠ ⊤ at h
    rw [hRbot] at h
    exact h (normalizer_eq_top (⊥ : Subgroup A))
  · intro P hSP hPA
    let := hb.solvable
    exact Group.isSolvable_of_isSolvable_injective
      (f := inclusion (hb.unique_maximal P (by simpa only [inf_comm A] using hSP) hPA))
      (inclusion_injective _)

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

private theorem bender_simple_pair_unique (S : Sylow 2 G) (A : Subgroup G)
    (hA : A.IsCComponent) (hmA : ClassificationModels.IsBenderModel A) [IsSimpleGroup A]
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
  let : IsSimpleGroup B := ((MulAut.conj s).subgroupMap A).symm.isSimpleGroup
  let := hA.perfect
  have hc : B ≤ centralizer (A : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (by
      rw [commutator_comm]
      exact simple_subnormal_commute_of_ne A B hA.subnormal hB.subnormal hm.symm)
  have hd := simple_pair_disjoint A B hc
  obtain ⟨huA,hneA,_⟩ := bender_sylow_interval S A hA.subnormal hmA
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_subnormal A hA.subnormal
  have hu := hasUniqueMaximalOver_of_simple_pair_sylow A B (S : Subgroup G)
    hc hd huA hneA S.isPGroup' P hP
    (fun g _ => NormPair.conjugate_eq_or_eq_of_normalizer_index_two hi hm g) s hs rfl
  have htop : (A ⊔ B) ⊔ (S : Subgroup G) = ⊤ :=
    top_unique (hgen ▸ sup_le_sup (le_sup_left : A ≤ A ⊔ B) le_rfl)
  rwa [htop] at hu

/-- A paired Bender component supplies uniqueness over its actual Sylow. -/
theorem bender_pair_sylow_unique
    (S : Sylow 2 G) (A : Subgroup G) (hA : A.IsCComponent)
    (hm : ClassificationModels.IsBenderModel (A ⧸ pCore 2 A))
    [IsSimpleGroup (A ⧸ pCore 2 A)]
    (hi : (normalizer (A : Set G)).index = 2)
    (hgen : A ⊔ (S : Subgroup G) = ⊤) :
    Order.HasUniqueMaximalOver (S : Subgroup G) ⊤ := by
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  let q := QuotientGroup.mk' (pCore 2 G)
  let Abar := A.map q
  let Sbar := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hAb : Abar.IsCComponent := hA.map_quotient (pCore 2 G)
  let e := cComponentTwoCoreQuotientEquiv hA
  let : IsSimpleGroup Abar := e.symm.isSimpleGroup
  have hmb := hm.of_mulEquiv e.symm
  have hib : (normalizer (Abar : Set (G ⧸ pCore 2 G))).index = 2 :=
    (cComponent_normalizer_index_quotient hA (pCore 2 G)).trans hi
  have hgenb : Abar ⊔ (Sbar : Subgroup (G ⧸ pCore 2 G)) = ⊤ := by
    change A.map q ⊔ (S : Subgroup G).map q = ⊤
    rw [← Subgroup.map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  exact hasUniqueMaximalOver_of_surjective q (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal S)
    (bender_simple_pair_unique Sbar Abar hAb hmb hib hgenb)

variable {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- Borel uniqueness applies to the literal join, independently of the seed. -/
theorem uniqueMaximalOver_of_bender
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hm : ClassificationModels.IsBenderModel (L ⧸ pCore 2 L)) :
    Order.HasUniqueMaximalOver (T : Subgroup G) (localJoin T L) := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let A := L.subgroupOf H
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  have hA : A.IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  let a := subgroupOfEquivOfLe hLH
  let e := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let := SmallOffender.Recognition.FixedSpaces.quotient_simple D hn
  let : IsSimpleGroup (A ⧸ pCore 2 A) := e.isSimpleGroup
  have hi : (normalizer (A : Set H)).index = 2 := by
    change (normalizer (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔
      (T : Subgroup G)) : Set (componentOrbit L (T : Subgroup G) ⊔
      (T : Subgroup G) : Subgroup G))).index = 2
    rw [componentOrbit_sup]
    exact source_nonnormal_normalizer_index D.simpleQTKE D.maximal.1 hn
  have hgen : A ⊔ (S : Subgroup H) = ⊤ := by
    change L.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
    rw [← subgroupOf_sup hLH (show (T : Subgroup G) ≤ H from le_sup_right)]
    rw [show L ⊔ (T : Subgroup G) = H from (componentOrbit_sup L (T : Subgroup G)).symm,
      subgroupOf_self]
  have hu := hasUniqueMaximalOver_map_subtype
    (bender_pair_sylow_unique S A hA (hm.of_mulEquiv e) hi hgen)
  have he : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  exact he ▸ hu

/-- The Bender source branches discharge the original stabilizer bound. -/
theorem stabilizer_normalizer_of_bender
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hm : ClassificationModels.IsBenderModel (L ⧸ pCore 2 L)) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤ D.maximalLocal :=
  stabilizer_normalizer_of_uniqueMaximalOver D hn (uniqueMaximalOver_of_bender D hn hm)

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
