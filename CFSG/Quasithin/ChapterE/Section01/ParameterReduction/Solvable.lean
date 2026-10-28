module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.QuotientFamily
public import Theory.GroupTheory.SolvableMinimalNormal

/-!
# Rank-one generation for solvable groups

We prove E.1.13 directly by induction through abelian minimal normal
p-subgroups. Quotient generation lifts modulo the minimal normal subgroup.
For p=2 that subgroup lies in the Sylow group. For odd p, E.1.10(6) places
each action commutator in the generated subgroup; minimal normality then
absorbs the kernel, or the kernel centralizes the entire weak closure.
Thus a positive generation witness is proved before taking the minimum.
This also closes the solvable branch used within the proof of E.1.11.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, E.1.7 and E.1.11--13, pp.210--214.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

/-- Rank-one generation for solvable groups, by abelian minimal normal factors. -/
theorem isEGenerated_one_of_solvable [Group.IsSolvable G] : IsEGenerated 1 G := by
  classical
  induction hn : Nat.card G using Nat.strong_induction_on generalizing G with
  | h n ih =>
    intro T Ω hΩ
    by_cases hG : (⊤ : Subgroup G) = ⊥
    · apply top_unique
      rw [hG]
      exact bot_le
    obtain ⟨U, p, hUn, hUne, _, hp, hUcomm, hpU, hmin⟩ :=
      exists_minimal_normal_abelian_pGroup (⊤ : Subgroup G) hG
    let _ := hUn
    let _ := hUcomm
    let _ : Fact p.Prime := ⟨hp⟩
    let _ : Nontrivial U := (nontrivial_iff_ne_bot U).mpr hUne
    have hlt : Nat.card (G ⧸ U) < n := by
      have hc : Nat.card U * Nat.card (G ⧸ U) = Nat.card G := U.card_mul_index
      have hu : 1 < Nat.card U := Finite.one_lt_card
      have hq : 0 < Nat.card (G ⧸ U) := Nat.card_pos
      nlinarith
    let M := eFamilySubgroup 1 (T : Subgroup G) Ω ⊔
      normalizer (weakClosure (T : Subgroup G) Ω : Set G)
    have hMU : M ⊔ U = ⊤ := generation_modulo_normal T hΩ U (ih _ hlt rfl)
    have hTM : (T : Subgroup G) ≤ M :=
      (sylow_le_weakClosure_normalizer T hΩ).trans le_sup_right
    suffices hUM : U ≤ M by
      change M = ⊤
      simpa only [sup_eq_left.mpr hUM] using hMU
    by_cases hp2 : p = 2
    · subst p
      exact (hpU.le_sylow_of_normal T).trans hTM
    have hcomm (A : Subgroup G) (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup G)) :
        ⁅U,A⁆ ≤ M := by
      let _ := hΩ.1 A hA
      have hAE : eSubgroup 1 (T : Subgroup G) A ≤ eFamilySubgroup 1 (T : Subgroup G) Ω :=
        le_iSup_of_le (⟨A, hA, hAT⟩ : {A : Subgroup G // A ∈ Ω ∧ A ≤ (T : Subgroup G)}) le_rfl
      exact (odd_normal_commutator_le_eSubgroup_one hp2 T U A hpU hAT).trans
        (hAE.trans le_sup_left)
    have hnormal : (U ⊓ M).Normal := by
      apply normalizer_eq_top_iff.mp
      apply top_unique
      rw [← hMU]
      apply sup_le
      · exact (le_inf (by rw [normalizer_eq_top]; exact le_top) M.le_normalizer).trans
          inf_normalizer_le_normalizer_inf
      · exact ((le_centralizer_iff_isMulCommutative.mpr hUcomm).trans
          (centralizer_le inf_le_left)).trans (centralizer_le_normalizer _)
    rcases hmin (U ⊓ M) hnormal inf_le_left with hbot | htop
    · have hUW : U ≤ centralizer (weakClosure (T : Subgroup G) Ω : Set G) := by
        apply le_centralizer_iff.mpr
        apply sSup_le
        intro A hA
        apply le_centralizer_iff.mp
        apply commutator_eq_bot_iff_le_centralizer.mp
        apply le_bot_iff.mp
        rw [← hbot]
        exact le_inf (commutator_le_left U A) (hcomm A hA.1 hA.2)
      exact (hUW.trans (centralizer_le_normalizer _)).trans le_sup_right
    · exact htop.symm.le.trans inf_le_right

/-- E.1.13, with a proved positive generation witness. -/
theorem generationParameter_le_one_of_solvable [Group.IsSolvable G] :
    generationParameter G ≤ 1 :=
  generationParameter_le Nat.zero_lt_one isEGenerated_one_of_solvable

/-- The minimum is attained and equals one for a finite solvable even-order group. -/
theorem generationParameter_eq_one_of_solvable [Group.IsSolvable G]
    (heven : ¬ Odd (Nat.card G)) : generationParameter G = 1 := by
  have h := generationParameter_spec heven ⟨1, Nat.zero_lt_one, isEGenerated_one_of_solvable⟩
  exact Nat.le_antisymm generationParameter_le_one_of_solvable h.1


end CFSG.Quasithin.ChapterE
