module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract
public import Theory.Representation.BinaryOffender.SmallDualOffender
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# B.5.13 in the binary linear-three source row

A binary natural three-space marking has dimension three. The outer alternatives
in B.5.1 have dimensions four, six, or six (symmetric degree at least five,
respectively the G₂ model), so the marked component is the whole group. The
resulting group is the binary projective special linear group, whose elementary
2-subgroups have rank at most two. A dual FF offender therefore has fixed
codimension at most two, and the small-dual-offender estimate gives the required
quadratic ratio bound on the original representation, including arbitrary fixed
summands.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.8 and
B.5.13, printed pp.91 and 111–112.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceB513
open QuasisimpleSource
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

private theorem natural_dimension {n : ℕ} (hlo : 5 ≤ n) (hhi : n ≤ 8) :
    Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin n)) =
      if n = 5 ∨ n = 6 then 4 else 6 := by
  interval_cases n <;>
    first
    | simpa using BinaryPermutation.finrank_natural_odd (Fin _) (by decide)
    | simpa using BinaryPermutation.finrank_natural_even (Fin _) (by decide)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem binary_linear_three_source_eq_top
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ L)
    (hnat : IsLinearNatural (c.sectionData.action.comp L.subtype) BinaryField.two 3) :
    L = ⊤ := by
  have hext : L = ⊤ ∨ OuterNaturalAction c.sectionData.action := by
    cases c.clause_one with
    | irreducible _ _ _ _ he => exact he.imp_right And.right
    | doubleThree _ hL _ _ _ => exact Or.inl hL
    | naturalDual _ _ hL _ => exact Or.inl hL
    | repeatedNatural _ _ _ _ _ hL _ => exact Or.inl hL
  rcases hext with hL | hext
  · exact hL
  obtain ⟨e⟩ := hnat
  have hdim := e.linearEquiv.finrank_eq
  change Module.finrank (ZMod 2) _ = Module.finrank (ZMod 2) (Fin 3 → ZMod 2) at hdim
  simp only [Module.finrank_pi, Fintype.card_fin] at hdim
  rcases hext with ⟨n, hn5, hn8, ⟨en⟩⟩ | ⟨eg⟩
  · have hd := en.linearEquiv.finrank_eq
    rw [natural_dimension hn5 hn8, hdim] at hd
    split_ifs at hd <;> contradiction
  · obtain ⟨eg⟩ := eg
    have hd := eg.linearEquiv.finrank_eq
    rw [Atlas.G2.Natural.finrank_space, hdim] at hd
    contradiction

private theorem quadraticRatio_le_two_of_twoRank_le_two
    (ρ : Representation (ZMod 2) G V) (hr : primeRank 2 G ≤ 2)
    (hff : IsFFModule ρ.dual) : quadraticRatio ρ ≤ 2 := by
  obtain ⟨A, hA⟩ := hff
  apply quadraticRatio_le_two_of_small_dual_offender ρ hA
  have hc := (primeRank_le_iff_elementary_card_le G).mp hr A hA.1.2
  have hh := Nat.log_mono_right (b := 2) hc
  simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh

/-- The binary natural three-space branch of B.5.13 on the literal dual. -/
theorem quadraticRatio_le_two_of_binary_linear_three_source
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ.dual L)
    (_hq : IsQuasisimple (generalizedFitting G))
    (_hn : ¬ IsCompl c.sectionData.space.toSubmodule (fixedSpace ρ.dual L))
    (hnat : IsLinearNatural (c.sectionData.action.comp L.subtype) BinaryField.two 3)
    (hff : IsFFModule ρ.dual) : quadraticRatio ρ ≤ 2 := by
  have hL := binary_linear_three_source_eq_top c hnat
  obtain ⟨e⟩ := hnat
  let eG : G ≃* Matrix.PSL3Two.PSL :=
    Subgroup.topEquiv.symm.trans
      ((MulEquiv.subgroupCongr hL.symm).trans (e.groupEquiv.trans Matrix.PSL3Two.equiv))
  apply quadraticRatio_le_two_of_twoRank_le_two ρ _ hff
  rw [primeRank_equiv 2 eG]
  exact (Matrix.PSL3Even.two_rank (ZMod 2) (by decide : 0 < 1) (by simp)).le

end CFSG.Quasithin.ChapterB.SourceB513
