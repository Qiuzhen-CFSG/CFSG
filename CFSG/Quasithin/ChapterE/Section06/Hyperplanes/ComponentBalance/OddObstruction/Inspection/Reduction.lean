module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Detection
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary

/-!
# Corank-two reduction of the complete E.6.8 alternatives

Alternatives (3) and (5) identify A with C_V(L) and give that fixed space
corank one, contradicting corank two. The Borel bound leaves exponents one
and two; Suzuki parameters are at least three. In the symplectic alternative,
the large Borel case forces exponent one, while the root case bounds it by
two. The explicit exceptional A₆ clause is retained independently of its
field presentation.

The small symplectic endpoint is converted using the actual equivalence
Sp₄(2)′ ≃ A₆, never by substituting the full Sp₄(2). All central two-covers
of L₃(4), fixed-field unitary parameters, and perfect alternating three-covers
remain in the output. The original Borel and symplectic records are also
retained in `inspection_alternatives` for consumers needing their other clauses.

These are reductions, not the completed E.6.19 inspection. Odd cores of the
three remaining model families' automorphism centralizers still have to be
calculated before concluding that L is A₇ or its central three-cover.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259), and E.6.19, printed p.252 (PDF p.263).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction
open Components Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] {M V A Q L : Subgroup G}

/-- Alternative (3) has the wrong corank at the specified subspace A. -/
theorem no_linear_four (hcorank : subgroupCorank V A = 2) :
    ¬ LinearFourAlternative M V A Q L := by
  intro d
  have he : subgroupCorank V A = 1 := by
    rw [d.fixed]
    exact d.dimension
  omega

/-- Alternative (5) has the wrong corank, including its PSL₂(5) overlap. -/
theorem no_odd_alternative (hcorank : subgroupCorank V A = 2) :
    ¬ OddAlternative M V A L := by
  intro d
  have he : subgroupCorank V A = 1 := by
    rw [d.fixed]
    exact d.dimension
  omega

/-- Actual models remaining in alternative (1), with the fixed-field PSU convention. -/
def SmallBorelModel (L : Subgroup G) : Prop :=
  ClassicalGroup.IsPSL L 2 2 ∨ ClassicalGroup.IsPSL L 2 4 ∨
  ClassicalGroup.IsPSL L 3 2 ∨ ClassicalGroup.IsPSL L 3 4 ∨
  ClassicalGroup.IsPSU L 3 2 ∨ ClassicalGroup.IsPSU L 3 4 ∨
  (IsPGroup 2 (center L) ∧ ClassicalGroup.IsPSL (L ⧸ center L) 3 4)

/-- Corank two bounds the field exponent and excludes every Suzuki parameter. -/
theorem borel_models {n : ℕ} (hcorank : subgroupCorank V A = 2)
    (d : BorelAlternative M V A L n) : (n = 1 ∨ n = 2) ∧ SmallBorelModel L := by
  have hb : n ≤ 2 := hcorank ▸ d.bound
  rcases d.model with ⟨hn, hm⟩ | ⟨m, hm, hn, hi⟩ | ⟨hn, hm⟩ |
      ⟨hn, hm⟩ | ⟨hn, hz, hm⟩
  · have hn' : n = 1 ∨ n = 2 := by omega
    refine ⟨hn', ?_⟩
    rcases hn' with rfl | rfl
    · exact Or.inl hm
    · exact Or.inr (Or.inl hm)
  · omega
  · have hn' : n = 1 ∨ n = 2 := by omega
    refine ⟨hn', Or.inr (Or.inr ?_)⟩
    rcases hn' with rfl | rfl
    · exact Or.inl hm
    · exact Or.inr (Or.inl hm)
  · have hn' : n = 1 ∨ n = 2 := by omega
    refine ⟨hn', Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩
    rcases hn' with rfl | rfl
    · exact Or.inl hm
    · exact Or.inr (Or.inl hm)
  · exact ⟨Or.inr hn, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr ⟨hz, hm⟩)))))⟩

/-- The symplectic exponent is one or two unless the explicit A₆ clause holds. -/
theorem symplectic_models {n : ℕ} (hcorank : subgroupCorank V A = 2)
    (d : SymplecticAlternative M V A L n) :
    n = 1 ∨ n = 2 ∨ IsAlternating L 6 := by
  have hb : actionCorank V L ≤ 2 := hcorank ▸ d.bound
  have hn : 1 ≤ n := d.model.1
  rcases d.local_structure with ⟨_, hd | ⟨hm, _⟩⟩ | ⟨_, _, hd⟩
  · left
    omega
  · exact Or.inr (Or.inr hm)
  · rcases (show n = 1 ∨ n = 2 by omega) with he | he
    · exact Or.inl he
    · exact Or.inr (Or.inl he)

/-- Retain the complete surviving source alternatives and their parameter bounds. -/
theorem inspection_alternatives (earlier : EarlierComponentAlternatives M V Q)
    (hA : A ∈ obstructionFamily M V) (hcorank : subgroupCorank V A = 2)
    (hL : CentralizerComponent A L) :
    (∃ n, BorelAlternative M V A L n ∧ (n = 1 ∨ n = 2) ∧ SmallBorelModel L) ∨
    (∃ n, SymplecticAlternative M V A L n ∧
      (n = 1 ∨ n = 2 ∨ IsAlternating L 6)) ∨
    IsAlternatingCover L 6 ∨ IsSeven L := by
  rcases (earlier A hA L hL).2 with ⟨n, hn⟩ | ⟨n, hn⟩ | hf | ha | ho
  · exact Or.inl ⟨n, hn, borel_models hcorank hn⟩
  · exact Or.inr (Or.inl ⟨n, hn, symplectic_models hcorank hn⟩)
  · exact (no_linear_four hcorank hf).elim
  · rcases ha.model with hs | hs | hs
    · exact Or.inr (Or.inr (Or.inr (Or.inl hs)))
    · exact Or.inr (Or.inr (Or.inl hs))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hs)))
  · exact (no_odd_alternative hcorank ho).elim

/-- Identify the small derived endpoint by its actual multiplicative equivalence. -/
theorem symplectic_small_models {n : ℕ} (hcorank : subgroupCorank V A = 2)
    (d : SymplecticAlternative M V A L n) :
    SymplecticDerivedModel L 2 ∨ IsAlternating L 6 := by
  rcases symplectic_models hcorank d with he | he | he
  · obtain ⟨_, F, _, _, hF, ⟨e⟩⟩ := d.model
    have hc : Nat.card F = 2 := by simpa only [he, pow_one] using hF
    exact Or.inr ⟨e.trans
      (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix hc)⟩
  · exact Or.inl (he ▸ d.model)
  · exact Or.inr he

/-- Only three intrinsic model calculations remain besides the desired seven models. -/
theorem remaining_models (earlier : EarlierComponentAlternatives M V Q)
    (hA : A ∈ obstructionFamily M V) (hcorank : subgroupCorank V A = 2)
    (hL : CentralizerComponent A L) :
    SmallBorelModel L ∨ SymplecticDerivedModel L 2 ∨
      IsAlternating L 6 ∨ IsAlternatingCover L 6 ∨ IsSeven L := by
  rcases inspection_alternatives earlier hA hcorank hL with
    ⟨n, _, _, hm⟩ | ⟨n, hd, _⟩ | hs | hs
  · exact Or.inl hm
  · rcases symplectic_small_models hcorank hd with hm | hm
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr (Or.inl hm))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hs)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hs)))

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction
