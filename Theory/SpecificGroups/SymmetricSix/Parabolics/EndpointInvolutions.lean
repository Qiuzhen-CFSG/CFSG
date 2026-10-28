module
public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.Reduction
/-!
# Involutions in the two S₆ parabolics

Two order-48 subgroups generating S₆ and containing a common order-16
subgroup are the incident duad and syntheme stabilizers, up to simultaneous
conjugation and exchange. The permutations (2 4) and (0 2)(1 3)(4 5)
lie outside their overlap and their product has order four. Transporting
this explicit pair gives the fixed-endpoint witnesses used in F.5.5.

Source: Aschbacher--Smith F.5.5, concluding paragraph, printed p.302.
-/
@[expose] public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymmetricSix

private def pairLeft : S6 := Equiv.swap 2 4
private def pairRight : S6 := Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 4 5

private theorem standard_pair :
    ∃ s t:S6, s∈duadStabilizer ∧ t∈synthemeStabilizer ∧
      s∉duadStabilizer⊓synthemeStabilizer ∧ t∉duadStabilizer⊓synthemeStabilizer ∧
      orderOf s=2 ∧ orderOf t=2 ∧ orderOf (s*t)=4 := by
  refine ⟨pairLeft,pairRight,by decide,by decide,(fun hh => (by decide : pairLeft ∉ synthemeStabilizer) hh.2),(fun hh => (by decide : pairRight ∉ duadStabilizer) hh.1),?_,?_,?_⟩
  · exact orderOf_eq_prime (by decide) (by decide)
  · exact orderOf_eq_prime (by decide) (by decide)
  · apply (orderOf_eq_iff (by decide : 0<4)).mpr
    constructor
    · decide
    · intro m hm hpos
      interval_cases m <;> decide

private theorem mapped_pair {X Y:Type*} [Group X] [Group Y]
    (e:X≃*Y) (H K:Subgroup X)
    (hp:∃s t:X,s∈H ∧ t∈K ∧ s∉H⊓K ∧ t∉H⊓K ∧
      orderOf s=2 ∧ orderOf t=2 ∧ orderOf (s*t)=4) :
    ∃s t:Y,s∈e.mapSubgroup H ∧ t∈e.mapSubgroup K ∧
      s∉e.mapSubgroup H⊓e.mapSubgroup K ∧ t∉e.mapSubgroup H⊓e.mapSubgroup K ∧
      orderOf s=2 ∧ orderOf t=2 ∧ orderOf (s*t)=4 := by
  obtain ⟨s,t,hs,ht,hsout,htout,hs2,ht2,hst⟩:=hp
  refine ⟨e s,e t,mem_map_of_mem _ hs,mem_map_of_mem _ ht,?_,?_,?_,?_,?_⟩
  · intro hh
    apply hsout
    exact ⟨by simpa using (mem_map_equiv).mp hh.1,by simpa using (mem_map_equiv).mp hh.2⟩
  · intro hh
    apply htout
    exact ⟨by simpa using (mem_map_equiv).mp hh.1,by simpa using (mem_map_equiv).mp hh.2⟩
  · simpa only [e.orderOf_eq] using hs2
  · simpa only [e.orderOf_eq] using ht2
  · simpa only [←e.map_mul,e.orderOf_eq] using hst

theorem pair_of_common_sixteen (H K P:Subgroup S6)
    (hP:Nat.card P=16) (hH:Nat.card H=48) (hK:Nat.card K=48)
    (hPH:P≤H) (hPK:P≤K) (hgen:H⊔K=⊤) :
    ∃s t:S6,s∈H ∧ t∈K ∧ s∉H⊓K ∧ t∉H⊓K ∧
      orderOf s=2 ∧ orderOf t=2 ∧ orderOf (s*t)=4 := by
  have hidx:P.index=45 := by
    have hh:=P.card_mul_index
    rw [hP,s6_order] at hh
    omega
  let T:Sylow 2 S6:=(IsPGroup.of_card (show Nat.card P=2^4 by omega)).toSylow
    (by rw [hidx]; decide)
  have hrel (J:Subgroup S6) (hPJ:P≤J) (hJ:Nat.card J=48):P.relIndex J=3 := by
    have hh:=relIndex_mul_relIndex (⊥:Subgroup S6) P J bot_le hPJ
    simp only [relIndex_bot_left,hP,hJ] at hh
    omega
  obtain ⟨g,hg⟩:=ResidualPairRecognition.pair_conjugate T H K hPH hPK
    (hrel H hPH hH) (hrel K hPK hK) hgen
  have hp:=mapped_pair (MulAut.conj g) duadStabilizer synthemeStabilizer standard_pair
  rcases hg with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact hp
  · obtain ⟨s,t,hs,ht,hsout,htout,hs2,ht2,hst⟩:=hp
    refine ⟨t,s,ht,hs,?_,?_,ht2,hs2,?_⟩
    · simpa only [inf_comm] using htout
    · simpa only [inf_comm] using hsout
    · exact (SemiconjBy.orderOf_eq t (show SemiconjBy t (s*t) (t*s) from (mul_assoc t s t).symm)).symm.trans hst

theorem pair_of_equiv_symmetricSix {X:Type*} [Group X]
    (e:X≃*S6) (H K P:Subgroup X)
    (hP:Nat.card P=16) (hH:Nat.card H=48) (hK:Nat.card K=48)
    (hPH:P≤H) (hPK:P≤K) (hgen:H⊔K=⊤) :
    ∃s t:X,s∈H ∧ t∈K ∧ s∉H⊓K ∧ t∉H⊓K ∧
      orderOf s=2 ∧ orderOf t=2 ∧ orderOf (s*t)=4 := by
  have hp:=pair_of_common_sixteen (e.mapSubgroup H) (e.mapSubgroup K) (e.mapSubgroup P)
    ((card_map_of_injective e.injective).trans hP)
    ((card_map_of_injective e.injective).trans hH)
    ((card_map_of_injective e.injective).trans hK)
    (e.mapSubgroup.monotone hPH) (e.mapSubgroup.monotone hPK)
    (by rw [←e.mapSubgroup.map_sup,hgen,e.mapSubgroup.map_top])
  simpa using mapped_pair e.symm (e.mapSubgroup H) (e.mapSubgroup K) hp
end Theory.SpecificGroups.SymmetricSix
