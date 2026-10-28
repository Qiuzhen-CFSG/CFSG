module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.ModelTypes
public import Theory.SpecificGroups.PSL3.OddDegreeProjectiveComparison
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.SpecificGroups.ThreeDivisibility.Classical
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.GroupTheory.PrimeRankZero

/-!
# Intrinsic facts about the surviving external carriers

Each of the three actual projective groups in `ExternalCarrier` has trivial
center and order divisible by three. The center computations use the scalar
center for SL₂, perfection of SL₃, and the concrete projective centralizer for
SU₃. Explicit cubic elements supply three-divisibility. Hence a bound of one
on three-rank is an equality.

The surviving parameters also identify the actual special and projective
groups through their canonical maps. This gives special matrix models for
the natural-module consumer without changing the projective output list.
These are consequences of `ExternalCarrier`; excluding the other members
of `HigherFieldCarrier` still requires their rank-two witnesses.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.20(a), printed p.954 (PDF p.971).
-/

public section

open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure
open Chapter1.Section02.LocalModels
open BenderSuzuki.MatrixGroups.HermitianForm
universe u
variable {D : Type u} [Group D]

private theorem center_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center B = ⊥) : center A = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro x hx
  apply e.injective
  have h := (Subgroup.centerCongr e ⟨x, hx⟩).property
  have he : (Subgroup.centerCongr e ⟨x, hx⟩ : B) = e x := rfl
  rw [he, hz, mem_bot] at h
  simpa only [map_one] using h

/-- Every surviving actual carrier is centerless. -/
theorem ExternalCarrier.center_eq_bot (h : ExternalCarrier D) : center D = ⊥ := by
  cases h with
  | linearTwo n hn iso =>
      obtain ⟨F, hfield, hfin, hF, ⟨e⟩⟩ := iso
      let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      apply center_transport (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm)
      exact Theory.PSL2.sl2_center_eq_bot F
  | linearThree n hn ho iso =>
      obtain ⟨F, hfield, hfin, hF, ⟨e⟩⟩ := iso
      let := Atlas.sl_perfect (F := F) 3 (by decide)
      exact center_transport e (Group.IsPerfect.center_quotient_center_eq_bot SL(3,F))
  | unitaryThree n hn he iso =>
      obtain ⟨F, hfield, hfin, J, hF, hconj, ⟨e⟩⟩ := iso
      exact center_transport e (EvenProjectiveComparison.center_eq_bot J (by omega) hF hconj)

/-- Genuine cubic elements in the matrix groups survive their scalar quotients. -/
theorem ExternalCarrier.three_dvd_card (h : ExternalCarrier D) : 3 ∣ Nat.card D := by
  cases h with
  | linearTwo n hn iso =>
      obtain ⟨F, hfield, hfin, hF, ⟨e⟩⟩ := iso
      rw [Nat.card_congr e.toEquiv]
      exact ProjectiveSpecialLinearGroup.three_dvd_card F 2 (by decide)
  | linearThree n hn ho iso =>
      obtain ⟨F, hfield, hfin, hF, ⟨e⟩⟩ := iso
      rw [Nat.card_congr e.toEquiv]
      exact ProjectiveSpecialLinearGroup.three_dvd_card F 3 (by decide)
  | unitaryThree n hn he iso =>
      obtain ⟨F, hfield, hfin, J, hF, hconj, ⟨e⟩⟩ := iso
      rw [Nat.card_congr e.toEquiv]
      exact Theory.SpecificGroups.ThreeDivisibility.unitary_three_dvd J n (by omega) hF hconj

/-- The source upper bound is sharp on every surviving model. -/
theorem ExternalCarrier.threeRank_eq_one [Finite D] (h : ExternalCarrier D)
    (hr : primeRank 3 D ≤ 1) : primeRank 3 D = 1 := by
  have hne : primeRank 3 D ≠ 0 := fun hz =>
    (PrimeRank.eq_zero_iff_not_dvd_card.mp hz) h.three_dvd_card
  omega

/-- The surviving projective models have genuine special matrix realizations,
with the same field parameters, for the natural-module argument. -/
theorem ExternalCarrier.specialModels (h : ExternalCarrier D) :
    (∃ n, 1 < n ∧ IsSL D 2 (2 ^ n)) ∨
      (∃ n, 1 < n ∧ Odd n ∧ IsSL D 3 (2 ^ n)) ∨
      (∃ n, 1 < n ∧ Even n ∧ IsSU D 3 (2 ^ n)) := by
  cases h with
  | linearTwo n hn iso =>
      obtain ⟨F, hfield, hfin, hF, ⟨e⟩⟩ := iso
      let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      exact Or.inl ⟨n, hn, F, hfield, hfin, hF,
        ⟨e.trans (Theory.PSL2.sl2QuotientEquiv F).symm⟩⟩
  | linearThree n hn ho iso =>
      obtain ⟨F, hfield, hfin, hF, ⟨e⟩⟩ := iso
      exact Or.inr (Or.inl ⟨n, hn, ho, F, hfield, hfin, hF,
        ⟨e.trans (PSL3.OddDegreeProjectiveComparison.specialProjectiveEquiv hF ho).symm⟩⟩)
  | unitaryThree n hn he iso =>
      obtain ⟨F, hfield, hfin, J, hF, hconj, ⟨e⟩⟩ := iso
      exact Or.inr (Or.inr ⟨n, hn, he, F, hfield, hfin, J, hF, hconj,
        ⟨e.trans (EvenProjectiveComparison.specialProjectiveEquiv J he hconj).symm⟩⟩)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure

end
