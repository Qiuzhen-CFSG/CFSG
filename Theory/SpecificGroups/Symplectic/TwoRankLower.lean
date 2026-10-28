module

public import Theory.SpecificGroups.Symplectic.TwoRankLower.Odd
public import Theory.SpecificGroups.SymplecticFour.DefiningRank
public import Mathlib.FieldTheory.Finite.Basic
/-!
# Two-rank of every higher symplectic model

Diagonal symplectic shears embed the additive field in each coordinate of
the actual central quotient. In characteristic two they give rank at least
three in half-dimension at least three. The symmetric two-by-two shears
supply the missing rank-two case. Combined with the odd-characteristic sign
and J construction, every PSp₂r with r ≥ 2 contains an elementary eight.
Source: Aschbacher–Smith A.2.12, printed p.36.
-/

open Matrix
namespace Theory.SpecificGroups.Symplectic.TwoRank
open SymplecticRoot
noncomputable section
variable (F : Type*) [Field F]
private def diagonalShear (r : ℕ) : Multiplicative (Fin r → F) →* Sp r F where
  toFun v := ⟨fromBlocks 1 (diagonal v.toAdd) 0 1, by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    simp⟩
  map_one' := by apply Subtype.ext; simp [← fromBlocks_one]
  map_mul' v w := by
    apply Subtype.ext
    change fromBlocks 1 (diagonal (v.toAdd + w.toAdd)) 0 1 =
      fromBlocks 1 (diagonal v.toAdd) 0 1 * fromBlocks 1 (diagonal w.toAdd) 0 1
    rw [fromBlocks_multiply]
    simp [diagonal_add,add_comm]
private def projectiveShear (r : ℕ) := project.comp (diagonalShear F r)
private theorem projectiveShear_injective (r : ℕ) : Function.Injective (projectiveShear F r) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hc : diagonalShear F r x ∈ Subgroup.center (Sp r F) :=
    (QuotientGroup.eq_one_iff _).mp hx
  have he := Subgroup.mem_center_iff.mp hc (SymplecticGroup.symJ (Fin r) F)
  have hm := congrArg Subtype.val he
  change J (Fin r) F * fromBlocks 1 (diagonal x.toAdd) 0 1 =
    fromBlocks 1 (diagonal x.toAdd) 0 1 * J (Fin r) F at hm
  simp only [J, fromBlocks_multiply, one_mul, mul_one, zero_mul, mul_zero,
    mul_neg, add_zero, zero_add] at hm
  have hdiag : diagonal x.toAdd = 0 := (fromBlocks_inj.mp hm).1.symm
  change x.toAdd = 0
  funext i
  simpa using congrArg (fun M : Matrix (Fin r) (Fin r) F => M i i) hdiag
private theorem defining_rank_ge [Finite F] (r : ℕ) {p e : ℕ} [Fact p.Prime] [CharP F p]
    (hcard : Nat.card F = p ^ e) : r * e ≤ primeRank p (PSp r F) := by
  apply primeRank_ge_of_elementary_embedding (f := projectiveShear F r)
  · intro x
    change p • x.toAdd = 0
    ext i
    simp [nsmul_eq_mul]
  · change Nat.card (Fin r → F) = p ^ (r * e)
    rw [Nat.card_fun, Nat.card_fin, hcard, ← pow_mul, Nat.mul_comm e r]
  · exact projectiveShear_injective F r
private theorem even_rank_ge [Finite F] [CharP F 2] {r : ℕ} (hr : 2 ≤ r) : 3 ≤ primeRank 2 (PSp r F) := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨e,_,he⟩ := FiniteField.card F 2
  have hcard : Nat.card F = 2 ^ (e : ℕ) := by simpa only [Nat.card_eq_fintype_card] using he
  by_cases h2 : r = 2
  · subst r
    have hb := SymplecticFour.DefiningRank.three_mul_fieldExponent_le_primeRank F hcard
    change 3 * (e : ℕ) ≤ primeRank 2 (PSp 2 F) at hb
    have := e.pos
    omega
  · have hb := defining_rank_ge F r hcard
    have := e.pos
    have hre : r ≤ r * (e : ℕ) := Nat.le_mul_of_pos_right r e.pos
    omega
/-- The complete higher symplectic family has two-rank at least three, over every finite field. -/
public theorem three_le [Finite F] {r : ℕ} (hr : 2 ≤ r) :
    3 ≤ primeRank 2 (PSp r F) := by
  by_cases hF : (2:F) = 0
  · let : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr hF
    exact even_rank_ge F hr
  · exact odd_rank_ge F hr hF
end
end Theory.SpecificGroups.Symplectic.TwoRank
