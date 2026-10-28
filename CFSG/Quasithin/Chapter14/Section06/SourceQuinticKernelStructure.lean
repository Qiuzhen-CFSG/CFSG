module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFullCoreBound
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticCoreLayers
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Abelian full quintic kernel and the two possible core orders

The full centralizer C contains the original elementary U centrally. Since
|U| = 32 and |C| <= 64, its quotient by the center is cyclic and C is
abelian. The exact order-sixteen quotient Q/C leaves the paired possibilities
(|C|,|Q|) = (32,512) or (64,1024). No local Ree branch is discarded.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- The literal full quintic kernel is abelian, with exactly the two
paired kernel/core orders allowed by the local Ree alternatives. -/
theorem source_quintic_full_kernel_structure
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let U := conjugateSpanBy (localModule T M) H
    let Q := H.pCoreIn 2
    let C := H ⊓ centralizer (U : Set G)
    IsMulCommutative C ∧
      ((Nat.card C = 32 ∧ Nat.card Q = 512) ∨
       (Nat.card C = 64 ∧ Nat.card Q = 1024)) ∧
      (frattini C).map C.subtype ≤ centralInvolutions T ∧
      ⁅Q,Q⁆ = U ∧ (frattini Q).map Q.subtype = U := by
  classical
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  let : IsElementaryAbelian 2 U :=
    (Section02.SolvableAmalgam.source_index_five_closure_structure
      hG T hempty hM hu hmany hcard e H hH.1 hi).1
  have hUQ : U ≤ Q := by
    obtain ⟨he,F,hp,_,_,hloc⟩ := Section02.source_lemma_14_2_6
      hG T hempty hM hu hmany hcard e
    let := he
    obtain ⟨_,hl,_,_,_,_⟩ := hloc H hH.1
    have hh := hl.U_le_core
    change conjugateSpanBy (rankTwoSeed T M) H ≤ H.pCoreIn 2 at hh
    simpa only [Section02.rankTwoSeed_eq_localModule] using hh
  have hUC : U ≤ C := le_inf (hUQ.trans (pCoreIn_le 2 H)) (le_centralizer U)
  have hUcard : Nat.card U = 32 :=
    (source_quintic_span_card_and_core_radical hG T hempty hM hu hmany hcard e H hH hi).1
  have hCup : Nat.card C ≤ 64 :=
    (source_quintic_full_core_and_kernel_upper hG T hempty hM hu hmany hcard e H hH hi).2.2
  have hUcenter : U.subgroupOf C ≤ center C := by
    intro u hu
    rw [mem_center_iff]
    intro c
    exact Subtype.ext (((show C ≤ centralizer (U : Set G) from inf_le_right) c.property u hu).symm)
  have hZcard : 32 ≤ Nat.card (center C) := by
    have hh := card_le_of_le hUcenter
    rw [Nat.card_congr (subgroupOfEquivOfLe hUC).toEquiv,hUcard] at hh
    exact hh
  have hquot : Nat.card (C ⧸ center C) ≤ 2 := by
    have hh := (center C).card_mul_index
    rw [index_eq_card] at hh
    nlinarith
  have hpos : 0 < Nat.card (C ⧸ center C) := Nat.card_pos
  have hdiv : Nat.card (C ⧸ center C) ∣ 2 := by
    have hh : Nat.card (C ⧸ center C) = 1 ∨ Nat.card (C ⧸ center C) = 2 := by omega
    rcases hh with h | h <;> simp [h]
  let : IsCyclic (C ⧸ center C) := isCyclic_of_card_dvd_prime (p := 2) hdiv
  have hcomm : IsMulCommutative C := isMulCommutative_of_isCyclic_quotient_center_self C
  have hCQ : C ≤ Q := source_quintic_span_centralizer_le_core hG T hM H hH hi
  have hpC : IsPGroup 2 C := (isPGroup_pCoreIn 2 H).to_le hCQ
  have hClow : 32 ≤ Nat.card C := hUcard ▸ card_le_of_le hUC
  obtain ⟨n,hn⟩ := hpC.exists_card_eq
  have hCcases : Nat.card C = 32 ∨ Nat.card C = 64 := by
    have hnle : n ≤ 6 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      (by simpa only [hn] using hCup)
    have hnge : 5 ≤ n := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      (by simpa only [hn] using hClow)
    have hncase : n = 5 ∨ n = 6 := by omega
    rcases hncase with hn5 | hn6
    · norm_num [hn5] at hn
      exact Or.inl hn
    · norm_num [hn6] at hn
      exact Or.inr hn
  obtain ⟨_,hN,_,hCquot,_⟩ := source_quintic_second_kernel_card_sixteen
    hG T hempty hM hu hmany hcard e H hH hi
  let := hN
  have hcardQC := (C.subgroupOf Q).card_mul_index
  rw [index_eq_card] at hcardQC
  change Nat.card (C.subgroupOf Q) * Nat.card (Q ⧸ C.subgroupOf Q) = Nat.card Q at hcardQC
  rw [hCquot,Nat.card_congr (subgroupOfEquivOfLe hCQ).toEquiv] at hcardQC
  have horders : (Nat.card C = 32 ∧ Nat.card Q = 512) ∨
      (Nat.card C = 64 ∧ Nat.card Q = 1024) := by
    rcases hCcases with h | h
    · exact Or.inl ⟨h,by omega⟩
    · exact Or.inr ⟨h,by omega⟩
  have hlayers := source_quintic_full_core_layers hG T hempty hM hu hmany hcard e H hH hi
  exact ⟨hcomm,horders,
    source_quintic_full_kernel_frattini_le_point hG T hempty hM hu hmany hcard e H hH hi,
    hlayers.1,hlayers.2.1⟩

end CFSG.Quasithin.Chapter14.Section06
