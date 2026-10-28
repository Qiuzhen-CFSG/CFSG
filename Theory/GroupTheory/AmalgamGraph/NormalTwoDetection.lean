module
public import Theory.GroupTheory.AmalgamGraph.SylowCenterSpan
public import Theory.GroupTheory.PGroup.NormalSubgroups

/-!
# Sylow-center detection of normal two-subgroups

A nontrivial normal two-subgroup of a finite local group meets the center
of a Sylow two-subgroup, hence contains an involution in its omega-center.
Consequently disjointness from the span of the Sylow omega-centers forces
it to vanish. The ambient completion need not be finite.

This is the normal-subgroup argument used for the Frattini subgroup in
DGS, *Groups and Graphs* (1985), 9.10(4), printed p.149.
-/

@[expose] public noncomputable section
open Subgroup
namespace Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G]

/-- A normal two-subgroup is detected by the actual Sylow-center span. -/
theorem normal_two_eq_bot_of_disjoint_sylowCenterSpan
    (P N : Subgroup G) [Finite P]
    (hNP : N ≤ P) (hp : IsPGroup 2 N)
    (hn : P ≤ normalizer (N : Set G))
    (hd : Disjoint N (sylowCenterSpan P)) : N = ⊥ := by
  let T : Sylow 2 P := Classical.choice inferInstance
  let U := (T : Subgroup P).map P.subtype
  let : (N.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hn
  have hpN : IsPGroup 2 (N.subgroupOf P) := hp.comap_subtype
  have hNT : N.subgroupOf P ≤ (T : Subgroup P) := hpN.le_sylow_of_normal T
  have hNU : N ≤ U := by
    intro n hnN
    exact mem_map.mpr ⟨⟨n,hNP hnN⟩,hNT hnN,rfl⟩
  have hUP : U ≤ P := map_subtype_le _
  let : Finite U := Finite.of_injective (inclusion hUP) (inclusion_injective _)
  let : Fact (IsPGroup 2 U) := ⟨T.isPGroup'.map P.subtype⟩
  let : (N.subgroupOf U).Normal := normal_subgroupOf_of_le_normalizer (hUP.trans hn)
  by_contra hN
  have hNUne : N.subgroupOf U ≠ ⊥ := by
    intro he
    have hm := map_subgroupOf_eq_of_le hNU
    rw [he,Subgroup.map_bot] at hm
    exact hN hm.symm
  obtain ⟨A,_,hAN,hcard,hAZ⟩ := exists_central_subgroup_card_eq_prime_in_normal
    (p := 2) (N.subgroupOf U) ((nontrivial_iff_ne_bot _).mpr hNUne)
  have hAbot : A = ⊥ := by
    apply bot_unique
    intro a ha
    have hp2 : a ^ 2 = 1 := by
      have hh : (⟨a,ha⟩ : A) ^ Nat.card A = 1 := pow_card_eq_one'
      rw [hcard] at hh
      exact congrArg A.subtype hh
    have haω : (a : G) ∈ omegaCenterIn U :=
      (mem_omegaCenterIn_iff _ _).mpr ⟨a.property,by
        intro u hu
        exact congrArg U.subtype ((mem_center_iff.mp (hAZ ha)) ⟨u,hu⟩),by
        exact congrArg U.subtype hp2⟩
    have haZ : (a : G) ∈ sylowCenterSpan P :=
      (show omegaCenterIn U ≤ sylowCenterSpan P from
        le_iSup (fun S : Sylow 2 P => omegaCenterIn ((S : Subgroup P).map P.subtype)) T) haω
    have ha1 : (a : G) = 1 := disjoint_def.mp hd (hAN ha) haZ
    exact mem_bot.mpr (Subtype.ext ha1)
  have hc : Nat.card A = 1 := card_eq_one.mpr hAbot
  omega

end Theory.GroupTheory.AmalgamGraph
