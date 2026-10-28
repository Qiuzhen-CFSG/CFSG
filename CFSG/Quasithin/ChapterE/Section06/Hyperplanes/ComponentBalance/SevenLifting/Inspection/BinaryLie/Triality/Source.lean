module

public import Theory.SpecificGroups.Triality.InvolutionFixedRank
public import Theory.SpecificGroups.Triality.InvolutionTwoComponents
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Triality

/-!
# The complete binary triality inspection in E.6.18

The actual inner involution has derived fixed three-rank at most one. Every
outer involution descends to the genuine triality carrier over the half-sized
field exponent; that smaller carrier is simple and perfect, including at
exponent one. These proved model facts discharge every triality input of the
seven-component inspection on the original automorphism and quotient map.

Source: Aschbacher–Smith E.6.18, printed p.252, using F.1.12(I)(4) and
16.1.4(1),(4), `refs/quasithin.pdf`.
-/

public section
open Subgroup Theory.GroupTheory
open Triality.Standard
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie

/-- All genuine binary triality carriers are simple and perfect. -/
theorem triality_models_source (n : ℕ) (hn : 0 < n) :
    IsSimpleGroup (BinaryCarrier n hn) ∧ Group.IsPerfect (BinaryCarrier n hn) :=
  ⟨inferInstance, inferInstance⟩

/-- The exact original inner actor satisfies the derived fixed-rank bound. -/
theorem triality_inner_source (n : ℕ) (hn : 0 < n)
    (a : MulAut (BinaryCarrier n hn)) (ha : orderOf a = 2)
    (hi : a ∈ MulAut.innerSubgroup (BinaryCarrier n hn)) :
    primeRank 3 (commutator a.fixedSubgroup) ≤ 1 :=
  Triality.Standard.InvolutionFixedRank.inner_fixed_derived_threeRank_le_one n hn a ha hi

/-- The original outer fixed group is the carrier at half the field exponent. -/
theorem triality_outer_source (n : ℕ) (hn : 0 < n)
    (a : MulAut (BinaryCarrier n hn)) (ha : orderOf a = 2)
    (hi : a ∉ MulAut.innerSubgroup (BinaryCarrier n hn)) :
    ∃ (m : ℕ) (hm : 0 < m), n = 2 * m ∧
      Nonempty (a.fixedSubgroup ≃* BinaryCarrier m hm) :=
  Triality.Standard.InvolutionTwoComponents.binary_outer_fixed_equiv n hn a ha hi

/-- Full triality model inspection, with all model and involution inputs discharged. -/
theorem triality_source {S : Type*} [Group S] (f : ℕ) (hf : 1 ≤ f)
    (hS : IsTrialityGroupAt (2 ^ f) S) : SevenActionInspection S := by
  apply triality_of_involution_data triality_models_source
    (fun n hn _ _ => triality_inner_source n hn) ?_ f hf hS
  intro n hn _ _ a ha hi
  obtain ⟨m, hm, hnm, he⟩ := triality_outer_source n hn a ha hi
  exact ⟨m, hm, by omega, he⟩

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie
