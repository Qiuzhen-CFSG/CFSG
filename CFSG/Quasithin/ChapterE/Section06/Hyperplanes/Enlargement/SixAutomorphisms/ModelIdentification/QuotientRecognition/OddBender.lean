module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Branches
public import Theory.SpecificGroups.Alternating.SixSubgroupObstructions
public import Theory.SpecificGroups.SU3.SixSubgroupExclusion
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import GorensteinWalter.PSL2CoprimeSylowCyclic
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.OddLie.LinearThreeFixed
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.OddLie.UnitaryThreeFixed

/-!
# Excluding fixed A₆ components in the odd and Bender catalogues

For odd PSL₂(pᵉ), e ≤ 2, cyclic Sylow three-subgroups exclude A₆ unless
p = 3; the remaining exact orders are handled directly, and an A₆ fixed
subgroup in PSL₂(9) fills the group and forces the actor to be identity.
This includes every involutory field action. PSL₃(3) is excluded by its
exact order. For the other odd linear-three and unitary-three models,
the genuine involution calculations bound the derived fixed group's
three-rank by one. A perfect A₆ component cannot embed there.

The Bender result is stronger: none of the actual carriers contains A₆.
Binary PSL₂ has abelian Sylow two-subgroups; binary PSU₃ has commuting
involutions in its root Sylow subgroup; Suzuki has order prime to three.
All transports use the model equivalences, and unitary parameters retain
the fixed-field convention. Both intrinsic contracts are proved below
without any additional premise. The full quotient catalogue is assembled
by the parent `QuotientRecognition` module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Theorem C and A.2.4, printed p.33; A.3.21(a), p.55; E.6.23, p.254
(PDF p.265). The imported matrix calculations use Huppert II.8.2–5,
II.10.4 and II.10.12, and GLS3 §§2.7 and 4.3.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open alternatingGroup.SixSubgroupObstructions
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen
universe u
variable {D : Type*} [Group D] [Finite D]

omit [Finite D] in
private theorem not_six_of_card_not_dvd (hD : ¬ 360 ∣ Nat.card D)
    (S : Subgroup D) : ¬ Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨e⟩
  have hc : Nat.card S = 360 := (Nat.card_congr e.toEquiv).trans card_six
  exact hD (hc ▸ S.card_subgroup_dvd_card)

/-- The full odd PSL₂ branch, retaining the degree-two field case and every endpoint. -/
theorem not_six_fixed_linear_two {p e : ℕ} (hp : p.Prime) (ho : Odd p)
    (he : e ≤ 2) (hD : ClassicalGroup.IsPSL D 2 (p ^ e))
    (a : MulAut D) (ha : orderOf a = 2) (S : Subgroup D)
    (hS : S ≤ a.fixedSubgroup) : ¬ Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨F, hfield, hfinite, hF, ⟨f⟩⟩ := hD
  let : Fact p.Prime := ⟨hp⟩
  have he0 : e ≠ 0 := by
    intro hz
    have h := Finite.one_lt_card (α := F)
    rw [hF, hz, pow_zero] at h
    omega
  have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) (hF ▸ ho.pow)
  have hcD : Nat.card D * 2 = p ^ e * ((p ^ e) ^ 2 - 1) := by
    rw [Nat.card_congr f.toEquiv, ← hF]
    exact hc
  by_cases hsmall : p ^ e < 7
  · have hp2 := hp.two_le
    have hpn2 : p ≠ 2 := fun h => by subst p; exact (by decide : ¬ Odd 2) ho
    have hp3 : 3 ≤ p := by omega
    have he1 : e = 1 := by
      have he2 : e = 1 ∨ e = 2 := by omega
      rcases he2 with h | h
      · exact h
      · subst e; nlinarith
    rw [he1, pow_one] at hcD hsmall
    have h35 : p = 3 ∨ p = 5 := by
      have hop : p % 2 = 1 := Nat.odd_iff.mp ho
      omega
    apply not_six_of_card_not_dvd _ S
    rcases h35 with rfl | rfl <;> norm_num at hcD <;> omega
  by_cases hp3 : p = 3
  · have he2 : e = 2 := by
      by_contra hn
      have he1 : e = 1 := by omega
      simp only [hp3, he1, pow_one] at hsmall
      omega
    have hcard : Nat.card D = 360 := by
      rw [hp3, he2] at hcD
      norm_num at hcD
      omega
    exact not_six_fixed_of_card hcard a ha S hS
  · let R : Sylow 3 PSL(2,F) := default
    have hcyc : IsCyclic R := GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card
      F hF (by omega) 3 (by decide) (by
        rw [hF]
        exact ((Nat.coprime_primes (by decide) hp).mpr (Ne.symm hp3)).pow_right e) R
    rintro ⟨s⟩
    exact not_injective_of_three_rank_le_one (R.primeRank_le_one_of_isCyclic hcyc)
      (f.toMonoidHom.comp (S.subtype.comp s.symm.toMonoidHom))
      (f.injective.comp (Subtype.val_injective.comp s.symm.injective))

omit [Finite D] in
/-- The characteristic-two linear groups contain no A₆ subgroup. -/
theorem not_six_binary_linear {n : ℕ} (hD : ClassicalGroup.IsPSL D 2 (2 ^ n))
    (S : Subgroup D) : ¬ Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨F, hfield, hfinite, hF, ⟨e⟩⟩ := hD
  let P : Sylow 2 PSL(2,F) := default
  obtain ⟨f⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hF P
  rintro ⟨s⟩
  apply not_injective_of_sylow_involutions_commute P
    (fun a b _ _ => ?_)
    (e.toMonoidHom.comp (S.subtype.comp s.symm.toMonoidHom))
    (e.injective.comp (Subtype.val_injective.comp s.symm.injective))
  exact f.symm.injective (by simp only [map_mul]; exact mul_comm _ _)

omit [Finite D] in
/-- The actual binary unitary models contain no A₆ subgroup. -/
theorem not_six_binary_unitary {n : ℕ} (hn : 0 < n)
    (hD : ClassicalGroup.IsPSU D 3 (2 ^ n))
    (S : Subgroup D) : ¬ Nonempty (S ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨E, hfield, hfinite, J, hcard, hconj, ⟨e⟩⟩ := hD
  rintro ⟨s⟩
  exact BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank.not_injective_alternating_six
    J hn hcard hconj (e.toMonoidHom.comp (S.subtype.comp s.symm.toMonoidHom))
    (e.injective.comp (Subtype.val_injective.comp s.symm.injective))

/-- All three Bender families satisfy the intrinsic fixed-component exclusion. -/
theorem benderFixedComponentExclusion : BenderFixedComponentExclusion.{u} := by
  intro D _ _ _ _ hD a ha S hS
  cases hD with
  | linear n hn iso => exact not_six_binary_linear iso S
  | unitary n hn iso => exact not_six_binary_unitary (by omega) iso S
  | suzuki m hm iso =>
    obtain ⟨e⟩ := iso
    apply not_six_of_card_not_dvd _ S
    intro hd
    have ht : 3 ∣ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
      rw [← Nat.card_congr e.toEquiv]
      exact (by decide : 3 ∣ 360).trans hd
    exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega) ht

/-- Assemble the odd branch from the intrinsic derived-fixed-group rank bounds. -/
theorem oddFixedComponentExclusion_of_rank
    (hlinear : ∀ (D : Type u) [Group D] [Finite D] [IsSimpleGroup D] [Group.IsPerfect D],
      ∀ p : ℕ, p.Prime → Odd p → p ≠ 3 → ClassicalGroup.IsPSL D 3 p →
        ComponentBalance.OddLie.InvolutionDerivedThreeRank D)
    (hunitary : ∀ (D : Type u) [Group D] [Finite D] [IsSimpleGroup D] [Group.IsPerfect D],
      ∀ p : ℕ, p.Prime → Odd p → ClassicalGroup.IsPSU D 3 p →
        ComponentBalance.OddLie.InvolutionDerivedThreeRank D) :
    OddFixedComponentExclusion.{u} := by
  intro D _ _ _ _ hD a ha S hS
  cases hD with
  | linear_two p e hp ho he iso => exact not_six_fixed_linear_two hp ho he iso a ha S hS.1
  | linear_three p hp ho iso =>
    by_cases hp3 : p = 3
    · subst p
      obtain ⟨F, hfield, hfinite, hF, ⟨f⟩⟩ := iso
      have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
      rw [hF] at hc
      norm_num [Fin.prod_univ_succ] at hc
      have hcard : Nat.card D = 5616 := by rw [Nat.card_congr f.toEquiv]; omega
      exact not_six_of_card_not_dvd (by rw [hcard]; decide) S
    · exact not_six_of_derived_fixed_rank a (hlinear D p hp ho hp3 iso a ha) S hS
  | unitary_three p hp ho iso =>
    exact not_six_of_derived_fixed_rank a (hunitary D p hp ho iso a ha) S hS

/-- The full odd catalogue satisfies the intrinsic fixed-component exclusion,
with the actual inner, graph and field cases discharged. -/
theorem oddFixedComponentExclusion : OddFixedComponentExclusion.{u} := by
  apply oddFixedComponentExclusion_of_rank
  · intro D _ _ _ _ p hp ho hp3 hD
    exact ComponentBalance.OddLie.involutionDerivedThreeRank_linear_three
      (Group.IsPerfect.not_isMulCommutative D) hp ho hp3 hD
  · intro D _ _ _ _ p hp ho hD
    exact ComponentBalance.OddLie.involutionDerivedThreeRank_unitary hp ho hD

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen
