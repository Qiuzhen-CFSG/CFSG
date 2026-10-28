module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramModelResidual
public import Theory.SpecificGroups.PSL3.SplitPrimeRank
public import Theory.SpecificGroups.PSL3Four.ThreeRank
public import Theory.SpecificGroups.SymplecticFour.SplitTorusRank
public import Theory.NumberTheory.BinaryMinusPrimeRestriction
public import Theory.GroupTheory.OddPrimeRankOneSylow

/-!
# An odd rank-two mark from the actual diagram quotient

The split rank-two tori in the nonbinary linear and symplectic models have
odd prime rank at least two. At PSL₃(4), the literal elementary nine supplies
the mark instead of the scalar quotient of the split torus. A perfect cover
onto the marked source image inherits the threshold two: an odd-rank-one
group has cyclic Sylow subgroups, and every quotient remains rank at most one.
No general rank monotonicity through arbitrary kernels is asserted.

Source: Aschbacher--Smith 14.2.9, printed p.983, using the actual models
in E.2.2(4), printed pp.215--216.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section02
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

private theorem rank_two_of_odd_surjective {D : Type*} [Group D] [Finite D]
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (f : G →* D)
    (hf : Function.Surjective f) (hr : 2 ≤ primeRank p D) : 2 ≤ primeRank p G := by
  by_contra h
  have hle : primeRank p G ≤ 1 := by omega
  let P : Sylow p G := Classical.choice inferInstance
  have hP := P.isCyclic_of_odd_of_primeRank_le_one ho hle
  have hD := P.primeRank_le_one_of_surjective hP f hf
  omega

private theorem linear_three_odd_rank_two
    {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ 2 ≤ primeRank p PSL(3,F) := by
  by_cases hn2 : n = 2
  · subst n
    let := Fintype.ofFinite F
    let := Fintype.ofFinite Matrix.PSL3Four.F
    let eF : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq
      (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
        Matrix.PSL3Four.card_F]; norm_num)
    refine ⟨3, by decide, by decide, ?_⟩
    rw [primeRank_congr 3 (Atlas.fieldEquivPSL 3 eF)]
    exact Matrix.PSL3Four.ThreeRank.three_rank_ge_two
  · by_cases hn3 : n = 3
    · subst n
      let : Fact (Nat.Prime 7) := ⟨by decide⟩
      exact ⟨7, by decide, by decide,
        Matrix.PSL3.SplitPrimeRank.projective_rank F (by decide) (by rw [hF]; decide)⟩
    · obtain ⟨p,hp,hp3,hd⟩ := Nat.BinarySignedTorus.exists_prime_gt_three_dvd_sub
        (by omega : 3 < n)
      let : Fact p.Prime := ⟨hp⟩
      refine ⟨p,hp,Nat.BinarySignedTorus.odd_of_dvd_sub (by omega) hd,?_⟩
      exact Matrix.PSL3.SplitPrimeRank.projective_rank F (by omega) (hF ▸ hd)

private theorem symplectic_four_odd_rank_two
    {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ 2 ≤ primeRank p (Sp4Derived F) := by
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (show Nat.card F - 1 ≠ 1 by omega)
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨p,hp,Nat.BinarySignedTorus.odd_of_dvd_sub (by omega) (hF ▸ hd),?_⟩
  rw [primeRank_congr p
    (Theory.SpecificGroups.SymplecticFour.derivedEquivFull_of_card_gt_two (by omega : 2 < Nat.card F))]
  exact Theory.SpecificGroups.SymplecticFour.split_torus_prime_rank hp hd

theorem diagramModel_odd_prime_rank_two
    (M K T : Subgroup G) {n : ℕ} (hn : 1 < n) (hm : DiagramModel M K T n) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ 2 ≤ primeRank p K := by
  have hs {D : Type} [Group D] [Finite D] (e : sourceImage M K ≃* D)
      (hr : ∃ p : ℕ, p.Prime ∧ Odd p ∧ 2 ≤ primeRank p D) :
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ 2 ≤ primeRank p K := by
    obtain ⟨p,hp,ho,hr⟩ := hr
    let : Fact p.Prime := ⟨hp⟩
    let f := e.toMonoidHom.comp ((QuotientGroup.mk' (sourceKernel M)).subgroupMap K)
    exact ⟨p,hp,ho,rank_two_of_odd_surjective ho f
      (e.surjective.comp ((QuotientGroup.mk' (sourceKernel M)).subgroupMap_surjective K)) hr⟩
  rcases hm with ⟨F,hfield,hfinite,hchar,_,hF,e,_,_⟩ | ⟨F,hfield,hfinite,hchar,_,hF,e,_,_⟩
  · exact hs e (linear_three_odd_rank_two (F := F) hn hF)
  · exact hs e (symplectic_four_odd_rank_two (F := F) hn hF)
end CFSG.Quasithin.Chapter14.Section02
