module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.Representation.QuadraticFourGroup.Recognition.FactorSylows.Linear
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.Quasithin.CoprimeRank
public import Theory.Alternating.PrimeRank

/-!
# Three-rank of χ₀ blocks

The odd Sylow subgroups in binary SL₂ are cyclic. The other χ₀ quotients
are A₃ and A₅, both of three-rank one. Removing the two-core preserves
three-rank, so every actual χ₀ block has three-rank at most one.
This separates χ₀ from the six-point stabilizer in C.1.29, printed p.134.
-/
public section
namespace CFSG.Quasithin.ChapterC
open Subgroup Theory.GroupTheory
variable {L : Type*} [Group L] [Finite L]

theorem IsChiZeroBlock.threeRank_le_one (h : IsChiZeroBlock L) : primeRank 3 L ≤ 1 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 L) pCore_isPGroup]
  rcases h with ⟨n, _, _, F, _, _, hF, _, hm⟩ | h | h
  · obtain ⟨e⟩ := hm.quotient_iso
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    rw [primeRank_congr 3 e]
    let P : Sylow 3 (Matrix.SpecialLinearGroup (Fin 2) F) := Classical.choice inferInstance
    apply P.primeRank_le_one_of_isCyclic
    exact Matrix.SL2.odd_pGroup_isCyclic_of_injective (F := F) P.isPGroup' (by decide)
      (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).subtype
      (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).subtype_injective
  · obtain ⟨e⟩ := h.2.2.quotient_iso
    rw [primeRank_congr 3 e,
      GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 3 3 (by decide) (by decide)]
  · obtain ⟨e⟩ := h.2.2.quotient_iso
    rw [primeRank_congr 3 e,
      GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 5 3 (by decide) (by decide)]
end CFSG.Quasithin.ChapterC
