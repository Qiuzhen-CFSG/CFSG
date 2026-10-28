module

public import Theory.SpecificGroups.Classical.LinearTwoRankLower.OddFour
public import Theory.SpecificGroups.Classical.LinearFundamental
public import Theory.SpecificGroups.PSL4.DefiningRank
public import Mathlib.FieldTheory.Finite.Basic
public import Theory.GroupTheory.QuasithinBasic

/-!
# Linear groups of degree at least four have two-rank at least three

In odd characteristic, the explicit signed degree-four matrices give elementary
eights in both SL₄ and PSL₄. In characteristic two, the three first-row root
parameters give elementary subgroups of rank three times the field exponent.
In every larger degree, an identity complementary block embeds actual SL₄
faithfully through the ambient central quotient.

Source: the complete known-simple two-rank sieve in Aschbacher–Smith A.2.12,
printed p.36. The proper-block inclusion avoids assuming that an embedding
of covering groups descends to an embedding of their central quotients.
-/

public section
open Matrix
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup.LinearTwoRank
variable (F : Type*) [Field F] [Finite F]

/-- Every finite-field PSL₄ has two-rank at least three. -/
theorem three_le_projective_four : 3 ≤ primeRank 2 PSL(4,F) := by
  by_cases hF : (2:F) = 0
  · let : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr hF
    let : Fintype F := Fintype.ofFinite F
    obtain ⟨n, _, hn⟩ := FiniteField.card F 2
    have hc : Nat.card F = 2 ^ (n : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
    have hr := Matrix.PSL4.DefiningRank.three_mul_fieldExponent_le_primeRank F hc
    have hn0 := n.pos
    omega
  · exact Matrix.PSL4.OddTwoRank.three_le_projectiveRank F hF

/-- The actual covering SL₄ also contains an elementary eight. -/
theorem three_le_special_four : 3 ≤ primeRank 2 SL(4,F) := by
  by_cases hF : (2:F) = 0
  · let : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr hF
    let : Fintype F := Fintype.ofFinite F
    obtain ⟨n, _, hn⟩ := FiniteField.card F 2
    have hc : Nat.card F = 2 ^ (n : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
    have hi : Function.Injective (Matrix.PSL4.DefiningRank.rowFourHom F) := by
      intro a b hab
      apply Matrix.PSL4.DefiningRank.projectiveRowFour_injective F
      exact congrArg (QuotientGroup.mk' (Subgroup.center SL(4,F))) hab
    have hr : 3 * (n:ℕ) ≤ primeRank 2 SL(4,F) := by
      apply primeRank_ge_of_elementary_embedding
        (f := Matrix.PSL4.DefiningRank.rowFourHom F) (hf := hi)
      · intro v
        change 2 • v.toAdd = 0
        ext i
        simp [nsmul_eq_mul,hF]
      · change Nat.card (Fin 3 → F) = _
        rw [Nat.card_fun,Nat.card_fin,hc,← pow_mul,Nat.mul_comm (n:ℕ) 3]
    have hn0 := n.pos
    omega
  · exact Matrix.PSL4.OddTwoRank.three_le_specialRank F hF

/-- All actual projective special linear groups of degree at least four have
an elementary eight, uniformly in the finite coefficient field. -/
theorem three_le_projectiveRank {n : ℕ} (hn : 4 ≤ n) :
    3 ≤ primeRank 2 (ProjectiveSpecialLinearGroup (Fin n) F) := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hn
  · exact three_le_projective_four F
  let d := n - 5
  let e : (Fin 4 ⊕ Fin (1+d)) ≃ Fin n :=
    finSumFinEquiv.trans (finCongr (by dsimp [d]; omega))
  let f : SL(4,F) →* ProjectiveSpecialLinearGroup (Fin n) F :=
    (LinearFundamental.projectiveReindex (F := F) e).toMonoidHom.comp
      (LinearFundamental.projectLeft (m := Fin 4) (n := Fin (1+d)))
  have hi : Function.Injective f :=
    (LinearFundamental.projectiveReindex (F := F) e).injective.comp
      LinearFundamental.projectLeft_injective
  exact (three_le_special_four F).trans (Theory.GroupTheory.primeRank_le_of_injective 2 f hi)

end Matrix.SpecialLinearGroup.LinearTwoRank
