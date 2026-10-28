module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.NormalizerOrder
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The original elementary-plane normalizer quotient is A6

The canonical hyperplane polarity embeds the literal normalizer/centralizer
quotient into S6. The source orbit and cubic stabilizer calculation give
order360, so the image is the unique index-two subgroup A6. The ambient
centralizer is exactly the original plane. Both actual planes are retained,
and a surjection with the literal plane kernel supplies the cubic-nine
exclusion in45.7.
Source: Aschbacher, Sporadic Groups (1994),45.6, printed p.244.
-/

@[expose] public noncomputable section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G:Type*} [Group G] [Finite G] {z:G}
namespace RootPair
variable (P:RootPair z)

theorem normalizer_quotient_equiv_A6 (h:IsType z) (V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16) :
    Nonempty ((normalizer (V:Set G) ⧸ V.subgroupOf (normalizer (V:Set G)))≃*alternatingGroup (Fin 6)) := by
  obtain ⟨φ,hφ⟩:=P.exists_injective_plane_six_action h V hV
  have hcard:Nat.card φ.range=360 :=
    (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm.trans (P.plane_normalizer_card h V hV).2
  have hi:φ.range.index=2 := by
    have hh:=φ.range.index_mul_card
    rw [hcard,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin] at hh
    norm_num at hh
    omega
  have hr:φ.range=alternatingGroup (Fin 6) := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi
  have hk:V.subgroupOf (normalizer (V:Set G))=NormalizerAction.C V := by
    change _=(Subgroup.centralizer (V:Set G)).subgroupOf (normalizer (V:Set G))
    rw [P.plane_centralizer h V hV]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk).trans
    ((MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hr))⟩

theorem normalizer_A6_surjection (h:IsType z) (V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16) :
    ∃f:normalizer (V:Set G)→*alternatingGroup (Fin 6),Function.Surjective f ∧
      f.ker=V.subgroupOf (normalizer (V:Set G)) := by
  obtain ⟨e⟩:=P.normalizer_quotient_equiv_A6 h V hV
  let q:=QuotientGroup.mk' (V.subgroupOf (normalizer (V:Set G)))
  refine ⟨e.toMonoidHom.comp q,e.surjective.comp (QuotientGroup.mk'_surjective _),?_⟩
  ext x
  change e (q x)=1 ↔ x∈V.subgroupOf (normalizer (V:Set G))
  rw [e.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff x

theorem exists_two_A6_normalizer_planes (h:IsType z) :
    ∃d:P.PlanePair,
      Nonempty ((normalizer (d.first:Set G) ⧸ d.first.subgroupOf (normalizer (d.first:Set G)))≃*alternatingGroup (Fin 6)) ∧
      Nonempty ((normalizer (d.second:Set G) ⧸ d.second.subgroupOf (normalizer (d.second:Set G)))≃*alternatingGroup (Fin 6)) := by
  obtain ⟨d⟩:=P.exists_planePair h
  exact ⟨d,P.normalizer_quotient_equiv_A6 h d.first
    ⟨d.first_le.trans le_sup_left,d.first_elementary,d.first_card⟩,
    P.normalizer_quotient_equiv_A6 h d.second
    ⟨d.second_le.trans le_sup_left,d.second_elementary,d.second_card⟩⟩
end RootPair

/-- The actual elementary-plane normalizer supplies the A6 section used to exclude the cubic nine case. -/
theorem IsType.exists_A6_section (h:IsType z) :
    ∃M:Subgroup G,∃f:M→*alternatingGroup (Fin 6),Function.Surjective f := by
  obtain ⟨P⟩:=h.exists_rootPair
  obtain ⟨d⟩:=P.exists_planePair h
  obtain ⟨f,hf,_⟩:=P.normalizer_A6_surjection h d.first
    ⟨d.first_le.trans le_sup_left,d.first_elementary,d.first_card⟩
  exact ⟨normalizer (d.first:Set G),f,hf⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree
