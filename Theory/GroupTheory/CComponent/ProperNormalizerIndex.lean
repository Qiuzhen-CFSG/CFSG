module
public import Theory.GroupTheory.CComponent.LocalQuotientOrder
public import Theory.GroupTheory.PerfectSmallNormalizer
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The core index of a proper component normalizer

A subgroup whose intrinsic two-core quotient is at least as large as that
of its overgroup supplements the overgroup's two-core. If it is perfect
and has normalizer index at most four on that core, its coset action is
solvable and the existing small-index theorem makes it normal. Minimality
in an intrinsic C-component then forces equality. For a proper subgroup,
the index is a power of two greater than four, hence at least eight.

The relative version retains literal ambient subgroups and normalizers.
It supplies the index bound for the proper component inclusion in
Aschbacher--Smith 14.6.24(3), printed pp.1040--1041, avoiding a separate
noncentral-chief-factor construction. The Chapter14 consumer applies it
to the same Kplus < K^g and the original opposite two-core.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A subgroup whose intrinsic two-core quotient is at least as large as
the ambient one supplements the actual ambient two-core. -/
theorem sup_twoCore_eq_top_of_quotient_card_le (B : Subgroup G)
    (hc : Nat.card (G ⧸ pCore 2 G) ≤ Nat.card (B ⧸ pCore 2 B)) :
    B ⊔ pCore 2 G = ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hkb : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let e := (q.subgroupMap B).pCoreQuotientEquiv (q.subgroupMap_surjective B) hkb
  have hle : Nat.card (G ⧸ pCore 2 G) ≤ Nat.card (B.map q) := by
    calc
      Nat.card (G ⧸ pCore 2 G) ≤ Nat.card (B ⧸ pCore 2 B) := hc
      _ = Nat.card (B.map q ⧸ pCore 2 (B.map q)) := Nat.card_congr e.toEquiv
      _ ≤ Nat.card (B.map q) := Nat.le_of_dvd Nat.card_pos (pCore 2 (B.map q)).card_quotient_dvd_card
  have he : B.map q = ⊤ := eq_top_of_card_eq _ (le_antisymm (card_le_card_group _) hle)
  have hh := congrArg (Subgroup.comap q) he
  simpa only [Subgroup.comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using hh

/-- The normalizer of a proper perfect subgroup in an intrinsic
C-component has index at least eight on the two-core when their
intrinsic two-core quotients have the same order. -/
theorem eight_le_twoCore_normalizer_index
    (hG : (⊤ : Subgroup G).IsCComponent) (B : Subgroup G)
    [Group.IsPerfect B] (hB : B ≠ ⊥) (hproper : B ≠ ⊤)
    (hc : Nat.card (G ⧸ pCore 2 G) ≤ Nat.card (B ⧸ pCore 2 B)) :
    8 ≤ (normalizer (B : Set G)).relIndex (pCore 2 G) := by
  let Q := pCore 2 G
  let N := normalizer (B : Set G)
  have hsup := sup_twoCore_eq_top_of_quotient_card_le B hc
  have hgt : 4 < N.relIndex Q := by
    by_contra! hs
    let : Group.IsNilpotent Q := (pCore_isPGroup (p := 2) (G := G)).isNilpotent
    let : Group.IsSolvable Q := inferInstance
    have hn : B.Normal := normal_of_perfect_of_solvable_supplement_of_small_normalizer B Q hsup hs
    have ht := hG.minimal B le_top hB inferInstance hn.isSubnormal
    exact hproper (top_le_iff.mp ht)
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
  obtain ⟨k,_,hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (hn ▸ (N.relIndex_dvd_card Q))
  have hthree : 3 ≤ k := by
    by_contra! hsmall
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show k ≤ 2 by omega)
    rw [hk] at hgt
    norm_num at hh
    omega
  rw [hk]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hthree

/-- Apply the normalizer bound to an actual normalizing actor. -/
theorem eight_le_twoCore_actor_index
    (hG : (⊤ : Subgroup G).IsCComponent) (B S : Subgroup G)
    [Group.IsPerfect B] (hB : B ≠ ⊥) (hproper : B ≠ ⊤)
    (hc : Nat.card (G ⧸ pCore 2 G) ≤ Nat.card (B ⧸ pCore 2 B))
    (hS : S ≤ normalizer (B : Set G)) :
    8 ≤ S.relIndex (pCore 2 G) :=
  (eight_le_twoCore_normalizer_index hG B hB hproper hc).trans
    (relIndex_le_of_le_left hS index_ne_zero_of_finite)
/-- The same index bound inside a literal ambient component, with all
normality and normalizer statements relative to their actual overgroups. -/
theorem eight_le_core_relIndex_of_proper_relative_cComponent
    (H B J S : Subgroup G) (hJH : J ≤ H)
    (hJ : (J.subgroupOf H).IsCComponent)
    [Group.IsPerfect B] (hB : B ≠ ⊥) (hBJ : B < J)
    (hc : Nat.card (J ⧸ pCore 2 J) ≤ Nat.card (B ⧸ pCore 2 B))
    (hS : S ≤ normalizer (B : Set G)) : 8 ≤ S.relIndex (J.pCoreIn 2) := by
  let e := subgroupOfEquivOfLe hBJ.le
  let : Group.IsPerfect (B.subgroupOf J) := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hne : B.subgroupOf J ≠ ⊥ := by
    intro he
    have hh := congrArg (Subgroup.map J.subtype) he
    rw [map_subgroupOf_eq_of_le hBJ.le,Subgroup.map_bot] at hh
    exact hB hh
  have hproper : B.subgroupOf J ≠ ⊤ := by
    intro he
    have hh := congrArg (Subgroup.map J.subtype) he
    rw [map_subgroupOf_eq_of_le hBJ.le,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hBJ.ne hh
  have hJtop : (⊤ : Subgroup J).IsCComponent := by
    simpa only [subgroupOf_self] using hJ.subgroupOf_of_le le_rfl hJH
  have hcard : Nat.card (J ⧸ pCore 2 J) ≤
      Nat.card (B.subgroupOf J ⧸ pCore 2 (B.subgroupOf J)) := by
    let eq := e.toMonoidHom.pCoreQuotientEquiv (p := 2) e.surjective
      (IsPGroup.ker_isPGroup_of_injective e.injective)
    rwa [Nat.card_congr eq.toEquiv]
  have hn : S.subgroupOf J ≤ normalizer (B.subgroupOf J : Set J) :=
    (comap_mono hS).trans (B.le_normalizer_comap J.subtype)
  have hi := eight_le_twoCore_actor_index hJtop (B.subgroupOf J) (S.subgroupOf J)
    hne hproper hcard hn
  have hQ : (J.pCoreIn 2).subgroupOf J = pCore 2 J :=
    Subgroup.comap_map_eq_self_of_injective J.subtype_injective _
  rwa [←hQ,relIndex_subgroupOf (pCoreIn_le 2 J)] at hi
end Subgroup
