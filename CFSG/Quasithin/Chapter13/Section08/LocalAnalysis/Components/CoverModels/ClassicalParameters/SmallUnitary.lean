module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels
public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.UnitarySubfields.Binary
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison

/-!
# The small unitary endpoint and even cover parameters

The actual PSU₃(2) matrix image is solvable by the proved order-72 argument.
The natural SU-to-PSU map has central, hence solvable, kernel, so SU₃(2)
is solvable as well. A quasisimple group is nontrivial and perfect, ruling
out this endpoint. All other even parameters already have the required
exponent and mod-three congruence in A.3.6.

Source: Aschbacher–Smith, A.3.6(2), printed p.43, and 13.8.17, p.953;
Huppert II.10.12 for the small projective matrix group.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.Components.CoverModels.ClassicalParameters
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open CFSG.Quasithin.Chapter13.Section08.Components.Models
open BenderSuzuki.MatrixGroups

/-- Solvability lifts from the actual PSU₃(2) image through its central scalar kernel. -/
theorem su3_two_isSolvable {G : Type*} [Group G] (h : IsSU G 3 2) : Group.IsSolvable G := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := h
  let : Group.IsSolvable (ProjectiveSpecialUnitaryMatrixGroup J) :=
    CFSG.Quasithin.MainConverse.UnitaryThreeSections.psu3_two_isSolvable
      ⟨F, inferInstance, inferInstance, J, hcard, hconj, ⟨MulEquiv.refl _⟩⟩
  let : Group.IsSolvable (center J.specialSubgroup) :=
    Group.isSolvable_of_comm fun a b => IsMulCommutative.is_comm.comm a b
  let : Group.IsSolvable J.specialToProjective.ker :=
    Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective J.specialToProjective_ker_le_center)
  let : Group.IsSolvable J.specialSubgroup :=
    Group.isSolvable_of_ker_le_range J.specialToProjective.ker.subtype
      J.specialToProjective (by simp)
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

/-- Quasisimplicity excludes the fixed-field order-two unitary cover. -/
theorem not_su3_two {G : Type*} [Group G] [IsQuasisimple G] : ¬ IsSU G 3 2 := by
  let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
  let : Nontrivial G := Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (center G))
  intro h
  exact Group.IsPerfect.not_isSolvable G (su3_two_isSolvable h)

/-- The even branch of A.3.6 has exactly the exponent range required by 13.8.17. -/
theorem even_parameters {G : Type*} [Group G] [IsQuasisimple G]
    {unitary : Bool} {q : ℕ}
    (hq : ∃ n : ℕ, 1 ≤ n ∧ q = 2 ^ n ∧ q % 3 = if unitary then 2 else 1)
    (h : IsSLSign G unitary 3 q) :
    ∃ n : ℕ, ThreeParameter unitary n ∧ q = 2 ^ n ∧
      (2 ^ n) % 3 = if unitary then 2 else 1 := by
  obtain ⟨n, hn, rfl, hm⟩ := hq
  refine ⟨n, ?_, rfl, hm⟩
  cases unitary with
  | false => exact hn
  | true =>
    change 2 ≤ n
    by_contra hsmall
    have he : n = 1 := by omega
    subst n
    exact not_su3_two (by simpa [IsSLSign] using h)
end CFSG.Quasithin.Chapter13.Section08.Components.CoverModels.ClassicalParameters
