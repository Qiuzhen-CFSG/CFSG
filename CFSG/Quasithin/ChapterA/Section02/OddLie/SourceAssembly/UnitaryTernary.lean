module
public import CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly.UnitaryCaseII
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover.Rank
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover.ExceptionalThree

/-!
# Exact exceptional PSU₄(3) source inputs

The original odd-center cover has elementary three-center of order dividing
nine. Its actual four-dimensional root subgroup gives ordinary three-rank
at least three. Nontriviality of the source center identifies the offending
prime with three. These are proved inputs to the remaining partial-center
quotient argument, not a claim of local rank three.
Source: Aschbacher–Smith A.2.17 and I.2.1, printed pp.39 and 409.
-/

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
universe u
variable {K : GroupClass.{u}} {G S : Type u} [Group G] [Finite G] [Group S] [Finite S]
  [IsQuasisimple G] {p : ℕ}

public theorem unitary_four_ternary_source_inputs
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremsOnProperSections K G)
    (hP : IsPGroup p (center G))
    (model : ClassicalGroup.IsPSU (G ⧸ center G) 4 3) :
    p = 3 ∧ IsElementaryAbelian 3 (center G) ∧
      Nat.card (center G) ∣ 9 ∧ 3 ≤ primeRank 3 G := by
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨iso⟩⟩ := model
  have ho : Odd (Nat.card (center G)) := by
    let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
    obtain ⟨k,hk⟩ := hP.exists_card_eq
    rw [hk]
    exact h.2.2.2.2.2.1.pow
  obtain ⟨hZE,hZd⟩ :=
    Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover.center_elementary_three_and_card_dvd_nine
      J (by simpa using hcard) hconj iso ho
  have hZne : Nat.card (center G) ≠ 1 := fun hh =>
    h.center_ne_bot ih.theoremA ((center G).eq_bot_of_card_eq hh)
  have hd3 : 3 ∣ Nat.card (center G) := by
    have hcases := (Nat.dvd_prime_pow Nat.prime_three).mp (show Nat.card (center G) ∣ 3^2 from hZd)
    obtain ⟨k,hk,hkc⟩ := hcases
    rw [hkc]
    apply dvd_pow_self
    by_contra hh
    have hk0 : k = 0 := by omega
    exact hZne (by simpa only [hk0,pow_zero] using hkc)
  have hp3 : p = 3 := by
    let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
    obtain ⟨k,hk⟩ := hP.exists_card_eq
    rw [hk] at hd3
    exact ((Nat.dvd_prime h.2.2.2.2.1).mp
      (Nat.prime_three.dvd_of_dvd_pow hd3)).resolve_left (by decide) |>.symm
  refine ⟨hp3,hZE,hZd,?_⟩
  exact Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover.three_le_primeRank_of_quotient_equiv
    J Nat.prime_three (by decide) hcard hconj iso
end CFSG.Quasithin.ChapterA.Section02.OddLie.SourceAssembly
