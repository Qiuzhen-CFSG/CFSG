module
public import Stellmacher.ElementaryAbelianMaxFamilyMap
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Tactic
/-! # Normalizers of a two-member elementary maximum family
Conjugation permutes the intrinsic maximum elementary family. When it has two
members, each stabilizer has relative index at most two and contains the
Thompson subgroup. Inside a larger nilpotent group the normalizer condition
then gives a stabilizer with order at least that of the original subgroup.
All subgroup maps are the actual ambient conjugation maps.
Source application: Aschbacher--Smith 2.5.7, printed pp.555--556.
-/
public section
open Subgroup
namespace Stellmacher
variable {G:Type*} [Group G]

theorem maxFamily_conj_mem {S A:Subgroup G} (hA:A∈elementaryAbelianMaxSubgroups S)
    {x:G} (hx:x∈normalizer (S:Set G)) : A.conjBy x∈elementaryAbelianMaxSubgroups S := by
  have hm: S.map (MulAut.conj x).toMonoidHom=S:=mem_normalizer_iff_map_conj_eq.mp hx
  have hh: A.map (MulAut.conj x).toMonoidHom∈
      elementaryAbelianMaxSubgroups (S.map (MulAut.conj x).toMonoidHom):=
    (maxFamily_map_injective_iff _ (MulAut.conj x).injective S A).mpr hA
  rwa [hm] at hh

theorem normalizer_relIndex_eq_two_of_pair (S A B R:Subgroup G)
    (hpair:elementaryAbelianMaxSubgroups S={A,B}) (hne:A≠B)
    (hR:R≤normalizer (S:Set G)) {a:G} (ha:a∈R) (hswap:A.conjBy a=B) :
    (normalizer (A:Set G)).relIndex R=2 := by
  have hA:A∈elementaryAbelianMaxSubgroups S:=hpair.symm ▸ Set.mem_insert _ _
  have hB:B∈elementaryAbelianMaxSubgroups S:=hpair.symm ▸ Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hperm (b:G) (hb:b∈R) : A.conjBy b=A ∨ A.conjBy b=B := by
    have hh:=maxFamily_conj_mem hA (hR hb)
    simpa only [hpair, Set.mem_insert_iff, Set.mem_singleton_iff] using hh
  apply relIndex_eq_two_iff_exists_notMem_and.mpr
  refine ⟨a,ha,?_,?_⟩
  · intro hn
    exact hne ((mem_normalizer_iff_map_conj_eq.mp hn).symm.trans hswap)
  · intro b hb
    rcases hperm b hb with hfix | hmove
    · exact Or.inr (mem_normalizer_iff_map_conj_eq.mpr hfix)
    · left
      apply mem_normalizer_iff_map_conj_eq.mpr
      change A.conjBy (b*a)=A
      rw [conjBy_mul,hswap]
      have hBb:=maxFamily_conj_mem hB (hR hb)
      simp only [hpair,Set.mem_insert_iff,Set.mem_singleton_iff] at hBb
      rcases hBb with hgood | hbad
      · exact hgood
      · have he:A.conjBy b=B.conjBy b:=hmove.trans hbad.symm
        have ht:=congrArg (fun U:Subgroup G=>U.conjBy b⁻¹) he
        rw [conjBy_inv,conjBy_inv] at ht
        exact (hne ht).elim

theorem normalizer_relIndex_le_two_of_pair (S A B R:Subgroup G)
    (hpair:elementaryAbelianMaxSubgroups S={A,B}) (hne:A≠B)
    (hR:R≤normalizer (S:Set G)) : (normalizer (A:Set G)).relIndex R≤2 := by
  by_cases hfix:R≤normalizer (A:Set G)
  · rw [relIndex_eq_one.mpr hfix]; omega
  · obtain ⟨a,ha,hout⟩:=SetLike.not_le_iff_exists.mp hfix
    have hA:A∈elementaryAbelianMaxSubgroups S:=hpair.symm ▸ Set.mem_insert _ _
    have hh:=maxFamily_conj_mem hA (hR ha)
    simp only [hpair,Set.mem_insert_iff,Set.mem_singleton_iff] at hh
    have hswap:A.conjBy a=B:=hh.resolve_left (fun hf=>hout (mem_normalizer_iff_map_conj_eq.mpr hf))
    exact le_of_eq (normalizer_relIndex_eq_two_of_pair S A B R hpair hne hR ha hswap)

theorem maxJ_le_normalizer_of_pair (S A B:Subgroup G)
    (hpair:elementaryAbelianMaxSubgroups S={A,B}) (hne:A≠B) :
    elementaryAbelianMaxJ S≤normalizer (A:Set G) := by
  change sSup (elementaryAbelianMaxSubgroups S)≤_
  rw [hpair, sSup_insert, sSup_singleton]
  refine sup_le A.le_normalizer ?_
  intro b hb
  have hB:B∈elementaryAbelianMaxSubgroups S:=hpair.symm ▸ Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hA:A∈elementaryAbelianMaxSubgroups S:=hpair.symm ▸ Set.mem_insert _ _
  have hfixB:B.conjBy b=B:=mem_normalizer_iff_map_conj_eq.mp (B.le_normalizer hb)
  have hh:=maxFamily_conj_mem hA (S.le_normalizer (hB.1 hb))
  simp only [hpair,Set.mem_insert_iff,Set.mem_singleton_iff] at hh
  apply mem_normalizer_iff_map_conj_eq.mpr
  rcases hh with hh | hh
  · exact hh
  · have ht:=congrArg (fun U:Subgroup G=>U.conjBy b⁻¹) (hh.trans hfixB.symm)
    rw [conjBy_inv,conjBy_inv] at ht
    exact (hne ht).elim

theorem maxFamily_pair_map {Y:Type*} [Group Y] (f:G→*Y) (hf:Function.Injective f)
    (S A B:Subgroup G) (hpair:elementaryAbelianMaxSubgroups S={A,B}) :
    elementaryAbelianMaxSubgroups (S.map f)={A.map f,B.map f} := by
  ext D
  constructor
  · intro hD
    have he:(D.comap f).map f=D:=map_comap_eq_self (hD.1.trans (S.map_le_range f))
    have hh:(D.comap f)∈elementaryAbelianMaxSubgroups S:=by
      apply (maxFamily_map_injective_iff f hf S _).mp
      rwa [he]
    simp only [hpair,Set.mem_insert_iff,Set.mem_singleton_iff] at hh
    rcases hh with hh | hh
    · exact Set.mem_insert_iff.mpr (Or.inl (he.symm.trans (congrArg (fun U:Subgroup G=>U.map f) hh)))
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr (he.symm.trans (congrArg (fun U:Subgroup G=>U.map f) hh)))
  · intro hD
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hD
    rcases hD with rfl | rfl
    · apply (maxFamily_map_injective_iff f hf S A).mpr
      rw [hpair]; exact Set.mem_insert _ _
    · apply (maxFamily_map_injective_iff f hf S B).mpr
      rw [hpair]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

private theorem card_relIndex {A B:Subgroup G} (h:A≤B) :
    Nat.card A*A.relIndex B=Nat.card B := by
  have hh:=(A.subgroupOf B).card_mul_index
  rwa [Nat.card_congr (subgroupOfEquivOfLe h).toEquiv] at hh

variable [Finite G]

theorem mem_maxFamily_of_central_involution {S A:Subgroup G}
    (hA:A∈elementaryAbelianMaxSubgroups S) {z:G} (hz:z∈S)
    (hz2:z^2=1) (hzC:z∈centralizer (A:Set G)) : z∈A := by
  let : IsElementaryAbelian 2 A:=hA.2.1
  let : IsElementaryAbelian 2 (zpowers z):=IsElementaryAbelian.zpowers_of_pow_eq_one hz2
  let : IsElementaryAbelian 2 (A⊔zpowers z:Subgroup G):=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hzC)
  have he:A=A⊔zpowers z:=eq_of_le_of_card_ge le_sup_left
    (hA.2.2 _ (sup_le hA.1 (zpowers_le.mpr hz)) inferInstance)
  rw [he]
  exact mem_sup_right (mem_zpowers z)

theorem pair_normalizer_card_ge (S T A B:Subgroup G) [Group.IsNilpotent T]
    (hST:S<T) (hpair:elementaryAbelianMaxSubgroups S={A,B}) (hne:A≠B) :
    Nat.card S≤Nat.card (T⊓normalizer (S:Set G)⊓normalizer (A:Set G):Subgroup G) := by
  let N:=T⊓normalizer (S:Set G)
  let Q:=N⊓normalizer (A:Set G)
  have hSN:S≤N:=le_inf hST.le S.le_normalizer
  have hlt:S<N:=by
    refine lt_of_le_of_ne hSN ?_
    intro he
    have hproper:S.subgroupOf T<⊤:=by
      rw [lt_top_iff_ne_top,Ne,subgroupOf_eq_top]
      exact hST.not_ge
    have ht:=Group.normalizerCondition_of_isNilpotent (S.subgroupOf T) hproper
    obtain ⟨x,hx,hout⟩:=SetLike.exists_of_lt ht
    rw [←subgroupOf_normalizer_eq hST.le] at hx
    exact hout (show (x:G)∈S from he ▸ ⟨x.property,hx⟩)
  have hindex:2≤S.relIndex N:=by
    have hpos:0<S.relIndex N:=by
      have hc:=card_relIndex hSN
      have hn:=Nat.card_pos (α:=N)
      by_contra hh
      have hz:S.relIndex N=0:=by omega
      rw [hz,mul_zero] at hc
      omega
    have hne:S.relIndex N≠1:=fun hh=>hlt.not_ge (relIndex_eq_one.mp hh)
    omega
  have hdouble:2*Nat.card S≤Nat.card N:=by
    calc
      _≤Nat.card S*S.relIndex N:=by nlinarith
      _=Nat.card N:=card_relIndex hSN
  have hQi:Q.relIndex N≤2:=by
    change (N⊓normalizer (A:Set G)).relIndex N≤2
    rw [inf_relIndex_left]
    exact normalizer_relIndex_le_two_of_pair S A B N hpair hne inf_le_right
  have hcard:Nat.card N≤2*Nat.card Q:=by
    rw [←card_relIndex (show Q≤N from inf_le_left)]
    nlinarith
  change Nat.card S≤Nat.card Q
  omega

end Stellmacher
