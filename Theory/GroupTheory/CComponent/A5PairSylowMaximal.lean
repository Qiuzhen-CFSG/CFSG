module
public import Theory.SpecificGroups.Alternating.FiveSylowMaximal
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormSylow
public import Theory.GroupTheory.UniqueMaximalSimplePair

/-!
# Sylow maximality for a pair of A5 C-components

Suppose an A5 C-component has normalizer of index two and generates the
ambient finite group together with its specified Sylow two-subgroup. Modulo
the ambient two-core, the component and its other conjugate are disjoint
commuting simple factors. Each factor has a unique maximal subgroup over
its Sylow intersection. The paired-factor theorem gives unique maximality
in the quotient, which lifts because the two-core lies in the original Sylow.

This retains the original C-component and the full two-core. It supplies
the paired case of the minimal-parabolic assertion in Aschbacher–Smith,
The Classification of Quasithin Groups, 10.1.2(6), printed p.742.
-/

public section
open Subgroup
open Theory.GroupTheory
open Theory.SpecificGroups.Alternating.FiveSylowMaximal
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem five_sylow_intersection (S : Sylow 2 G) (A : Subgroup G)
    (hs : A.IsSubnormal) (e : A ≃* alternatingGroup (Fin 5)) :
    Order.HasUniqueMaximalOver (A ⊓ (S : Subgroup G)) A ∧ A ⊓ (S : Subgroup G) ≠ ⊥ := by
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_subnormal A hs
  have hu : Order.HasUniqueMaximalOver (P : Subgroup A) ⊤ :=
    hasUniqueMaximalOver_of_surjective e.toMonoidHom e.surjective
      (by rw [e.toMonoidHom.ker_eq_bot e.injective]; exact bot_le)
      (sylow_unique (P.mapSurjective e.surjective))
  have hum := hasUniqueMaximalOver_map_subtype hu
  rw [hP, subgroupOf_map_subtype, inf_comm] at hum
  refine ⟨hum, ?_⟩
  have hd : 2 ∣ Nat.card A := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
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

private theorem five_simple_pair_unique (S : Sylow 2 G) (A : Subgroup G)
    (hA : A.IsCComponent) (e : A ≃* alternatingGroup (Fin 5))
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
  let eB : B ≃* alternatingGroup (Fin 5) := ((MulAut.conj s).subgroupMap A).symm.trans e
  let : IsSimpleGroup A := e.isSimpleGroup
  let : IsSimpleGroup B := eB.isSimpleGroup
  let := hA.perfect
  have hc : B ≤ centralizer (A : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (by
      rw [commutator_comm]
      exact simple_subnormal_commute_of_ne A B hA.subnormal hB.subnormal hm.symm)
  have hd := simple_pair_disjoint A B hc
  obtain ⟨huA,hneA⟩ := five_sylow_intersection S A hA.subnormal e
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_subnormal A hA.subnormal
  have hu := hasUniqueMaximalOver_of_simple_pair_sylow A B (S : Subgroup G)
    hc hd huA hneA S.isPGroup' P hP
    (fun g _ => NormPair.conjugate_eq_or_eq_of_normalizer_index_two hi hm g) s hs rfl
  have htop : (A ⊔ B) ⊔ (S : Subgroup G) = ⊤ :=
    top_unique (hgen ▸ sup_le_sup (le_sup_left : A ≤ A ⊔ B) le_rfl)
  rwa [htop] at hu

/-- A paired A5 C-component supplies unique maximality over the original Sylow. -/
theorem IsCComponent.a5_pair_sylow_unique
    (S : Sylow 2 G) (A : Subgroup G) (hA : A.IsCComponent)
    (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5))
    (hi : (normalizer (A : Set G)).index = 2)
    (hgen : A ⊔ (S : Subgroup G) = ⊤) :
    Order.HasUniqueMaximalOver (S : Subgroup G) ⊤ := by
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  let q := QuotientGroup.mk' (pCore 2 G)
  let Abar := A.map q
  let Sbar := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hAb : Abar.IsCComponent := hA.map_quotient (pCore 2 G)
  let eb : Abar ≃* alternatingGroup (Fin 5) := (cComponentTwoCoreQuotientEquiv hA).symm.trans e
  have hib : (normalizer (Abar : Set (G ⧸ pCore 2 G))).index = 2 :=
    (cComponent_normalizer_index_quotient hA (pCore 2 G)).trans hi
  have hgenb : Abar ⊔ (Sbar : Subgroup (G ⧸ pCore 2 G)) = ⊤ := by
    change A.map q ⊔ (S : Subgroup G).map q = ⊤
    rw [← map_sup,hgen,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  exact hasUniqueMaximalOver_of_surjective q (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal S)
    (five_simple_pair_unique Sbar Abar hAb eb hib hgenb)

end Subgroup
