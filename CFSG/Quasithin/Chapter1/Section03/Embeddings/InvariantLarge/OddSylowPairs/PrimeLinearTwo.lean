module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddSylowPairs
public import Theory.SpecificGroups.PSL2.PrimeCoverCartanNormalizer
public import GorensteinWalter.LinearRingEquiv
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Prime-field linear-two exclusion for an actual odd complement

The prime-field odd rank bound transports through the coefficient-field
isomorphism and the actual model equivalence. Every odd-primary subgroup
is cyclic, contradicting the elementary-square or extraspecial-cube complement.
Chapter13 uses this for the Fermat–Mersenne row of the marked 1.1.5 catalogue.

Source: Aschbacher–Smith, 1.1.5(3)(e), pp.501–503; 13.1.12(3), p.875.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.HasOddSylowPair
variable {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]

/-- Every actual prime-field PSL₂ model excludes a noncyclic odd complement. -/
theorem not_prime_linear_two (h : HasOddSylowPair p A) (ho : Odd p)
    {q : ℕ} (hq : q.Prime) (hm : ClassicalGroup.IsPSL A 2 q) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fact q.Prime := ⟨hq⟩
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod q := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card,hF,ZMod.card])
  let j := e.trans (GorensteinWalter.psl2RingEquiv eF)
  have hr : primeRank p A ≤ 1 := by
    rw [primeRank_congr p j]
    exact Theory.PSL2.primeField_odd_rank ho
  obtain ⟨S,B,hB,_⟩ := h
  have hBr : primeRank p B ≤ 1 := (primeRank_subgroup_le p B).trans hr
  apply hB.not_isCyclic
  exact hB.isPGroup.isCyclic_of_odd_of_elementary_card_le ho (fun E he => by
    let := he
    exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hBr E)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.HasOddSylowPair
