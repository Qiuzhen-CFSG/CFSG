module
public import Theory.GroupTheory.SimplePairSolvability
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormSylow
public import Theory.SpecificGroups.SL2.SolvableSylowOvergroups
public import Theory.SpecificGroups.SL2.SylowBorelSeparation
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# Borel control in an exchanged pair of binary SL₂ components

Modulo the ambient two-core, the two components are commuting simple groups.
Every proper overgroup of the exchanging Sylow subgroup is solvable: its
projection to each factor normalizes a nontrivial proper intersection, hence
lies in that factor's unique Sylow Borel. Solvability lifts through the two-core.

Conversely, a solvable Sylow overgroup inside the product of the two simple
factors normalizes the original product Sylow, since both projections are
proper. These statements give the literal Borel placement in Aschbacher--Smith
10.2.3, printed p.745, for both the natural and orthogonal SL₂ rows.
Quasisimplicity is retained as an input from the original component.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup.ExchangedPair
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

private theorem sl2_sylow_intersection (S : Sylow 2 G) (A : Subgroup G)
    (hs : A.IsSubnormal) (e : A ≃* SL(2,F)) :
    Order.HasUniqueMaximalOver (A ⊓ (S : Subgroup G)) A ∧ A ⊓ (S : Subgroup G) ≠ ⊥ := by
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_subnormal A hs
  have hu : Order.HasUniqueMaximalOver (P : Subgroup A) ⊤ :=
    hasUniqueMaximalOver_of_surjective e.toMonoidHom e.surjective
      (by rw [e.toMonoidHom.ker_eq_bot e.injective]; exact bot_le)
      (sylow_hasUniqueMaximalOver 2 (P.mapSurjective e.surjective))
  have hum := hasUniqueMaximalOver_map_subtype hu
  rw [hP,subgroupOf_map_subtype,inf_comm] at hum
  refine ⟨hum,?_⟩
  intro he
  have hPbot : (P : Subgroup A) = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ A.subtype_injective).mp
    rw [hP,subgroupOf_map_subtype,inf_comm]
    exact he
  apply no_normal_sylow F 2 (P.mapSurjective (f := e.toMonoidHom) e.surjective)
  change ((P : Subgroup A).map e.toMonoidHom).Normal
  rw [hPbot,Subgroup.map_bot]
  infer_instance

private theorem sl2_intersection_overgroup_solvable
    (S : Sylow 2 G) (A : Subgroup G) (hs : A.IsSubnormal)
    (e : A ≃* SL(2,F))
    (P : Subgroup G) (hSP : A ⊓ (S : Subgroup G) ≤ P) (hP : P < A) :
    Group.IsSolvable P := by
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_subnormal A hs
  have hle : (R : Subgroup A) ≤ P.subgroupOf A := by
    rw [hR]
    intro a ha
    exact hSP ⟨a.property,ha⟩
  have hne : P.subgroupOf A ≠ ⊤ := fun he => hP.not_ge (subgroupOf_eq_top.mp he)
  have hmapne : (P.subgroupOf A).map e.toMonoidHom ≠ ⊤ := by
    intro he
    have hh := congrArg (comap e.toMonoidHom) he
    rw [comap_map_eq_self_of_injective e.injective,comap_top] at hh
    exact hne hh
  let := isSolvable_of_proper_sylow_overgroup (R.mapSurjective e.surjective)
    ((P.subgroupOf A).map e.toMonoidHom) (map_mono hle) hmapne
  let f := (subgroupOfEquivOfLe hP.le).symm.trans
    ((P.subgroupOf A).equivMapOfInjective e.toMonoidHom e.injective)
  exact Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective

variable [IsQuasisimple SL(2,F)]
local instance : IsSimpleGroup SL(2,F) := by
  let : IsSimpleGroup (SL(2,F) ⧸ center SL(2,F)) := IsQuasisimple.simple
  exact ((QuotientGroup.quotientMulEquivOfEq
    (Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot (F := F))).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup

private theorem simple_pair_proper_solvable (S : Sylow 2 G) (A : Subgroup G)
    (hA : A.IsCComponent) (e : A ≃* SL(2,F))
    (hi : (normalizer (A : Set G)).index = 2)
    (hgen : A ⊔ (S : Subgroup G) = ⊤)
    (V : Subgroup G) (hSV : (S : Subgroup G) ≤ V) (hV : V ≠ ⊤) :
    Group.IsSolvable V := by
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
  obtain ⟨huA,hneA⟩ := sl2_sylow_intersection S A hA.subnormal e
  obtain ⟨huB,hneB⟩ := sl2_sylow_intersection S B hB.subnormal eB
  have htop : (A ⊔ B) ⊔ (S : Subgroup G) = ⊤ :=
    top_unique (hgen ▸ sup_le_sup (le_sup_left : A ≤ A ⊔ B) le_rfl)
  let := S.isPGroup'.isNilpotent
  exact isSolvable_of_simple_pair_proper_overgroup A B (S : Subgroup G) V hc
    huA huB hneA hneB
    (conjugate_pair_permutation A B (S : Subgroup G) hm.symm
      (fun g _ => NormPair.conjugate_eq_or_eq_of_normalizer_index_two hi hm g) s hs rfl)
    ⟨s,hs,rfl⟩ (sl2_intersection_overgroup_solvable S A hA.subnormal e)
    (sl2_intersection_overgroup_solvable S B hB.subnormal eB)
    hSV (htop ▸ lt_top_iff_ne_top.mpr hV)

/-- Every proper Sylow overgroup in the exchanged component pair is solvable,
including the full ambient two-core. -/
theorem component_pair_proper_overgroup_solvable
    (S : Sylow 2 G) (A : Subgroup G) (hA : A.IsCComponent)
    (e : (A ⧸ pCore 2 A) ≃* SL(2,F))
    (hi : (normalizer (A : Set G)).index = 2)
    (hgen : A ⊔ (S : Subgroup G) = ⊤)
    (V : Subgroup G) (hSV : (S : Subgroup G) ≤ V) (hV : V ≠ ⊤) :
    Group.IsSolvable V := by
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
    rw [←Subgroup.map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hk : q.ker ≤ V := by
    rw [QuotientGroup.ker_mk']
    exact (pCore_isPGroup.le_sylow_of_normal S).trans hSV
  have hVb : V.map q ≠ ⊤ := by
    intro he
    have hh := congrArg (comap q) he
    rw [comap_map_eq_self hk,comap_top] at hh
    exact hV hh
  let := simple_pair_proper_solvable Sbar Abar hAb eb hib hgenb
    (V.map q) (map_mono hSV) hVb
  have hker : q.ker = pCore 2 G := QuotientGroup.ker_mk' _
  let : Group.IsSolvable q.ker := hker.symm ▸ inferInstance
  have h := isSolvable_comap_of_solvable_ker q (V.map q)
  rwa [comap_map_eq_self hk] at h

/-- A solvable overgroup of the literal product Sylow lies in its normalizer. -/
theorem pair_solvable_overgroup_le_sylow_normalizer
    (S : Sylow 2 (SL(2,F) × SL(2,F))) (P : Subgroup (SL(2,F) × SL(2,F)))
    [Group.IsSolvable P] (hSP : (S : Subgroup _) ≤ P) :
    P ≤ normalizer (S : Set _) := by
  let S1 := S.mapSurjective (f := MonoidHom.fst SL(2,F) SL(2,F)) (fun x => ⟨(x,1),rfl⟩)
  let S2 := S.mapSurjective (f := MonoidHom.snd SL(2,F) SL(2,F)) (fun x => ⟨(1,x),rfl⟩)
  have htwo : IsPGroup 2 ((S1 : Subgroup SL(2,F)).prod (S2 : Subgroup SL(2,F))) := by
    obtain ⟨a,ha⟩ := S1.isPGroup'.exists_card_eq
    obtain ⟨b,hb⟩ := S2.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (n := a+b) (by
      rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,Nat.card_prod,ha,hb,pow_add])
  have hle : (S : Subgroup _) ≤ (S1 : Subgroup SL(2,F)).prod (S2 : Subgroup SL(2,F)) := by
    intro x hx
    exact ⟨mem_map_of_mem (MonoidHom.fst _ _) hx,mem_map_of_mem (MonoidHom.snd _ _) hx⟩
  have he : (S : Subgroup _) = (S1 : Subgroup SL(2,F)).prod (S2 : Subgroup SL(2,F)) :=
    (S.is_maximal' htwo hle).symm
  have hproper (f : SL(2,F) × SL(2,F) →* SL(2,F)) : P.map f ≠ ⊤ := by
    intro hh
    have hsol : Group.IsSolvable (⊤ : Subgroup SL(2,F)) := hh ▸
      Group.isSolvable_of_surjective (f.subgroupMap_surjective P)
    let := hsol
    exact Group.IsPerfect.not_isSolvable SL(2,F)
      (Group.isSolvable_of_surjective (f := (topEquiv (G := SL(2,F))).toMonoidHom)
        (topEquiv (G := SL(2,F))).surjective)
  have h1 := proper_overgroup_le_sylow_normalizer S1 (P.map (MonoidHom.fst _ _))
    (map_mono hSP) (hproper _)
  have h2 := proper_overgroup_le_sylow_normalizer S2 (P.map (MonoidHom.snd _ _))
    (map_mono hSP) (hproper _)
  intro x hx
  have hx1 := h1 (mem_map_of_mem (MonoidHom.fst _ _) hx)
  have hx2 := h2 (mem_map_of_mem (MonoidHom.snd _ _) hx)
  rw [show (S : Set (SL(2,F) × SL(2,F))) = ((S1 : Subgroup SL(2,F)).prod (S2 : Subgroup SL(2,F)) : Set (SL(2,F) × SL(2,F)))
    from congrArg SetLike.coe he]
  apply mem_normalizer_iff.mpr
  rintro ⟨a,b⟩
  exact (mem_normalizer_iff.mp hx1 a).and (mem_normalizer_iff.mp hx2 b)
end Matrix.SpecialLinearGroup.ExchangedPair
