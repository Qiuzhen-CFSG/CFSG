module
public import Theory.SpecificGroups.GL2.TopDeterminantCentralLayer
public import Theory.SpecificGroups.GL2.DiagonalSwapExterior

/-!
# Actual exterior elements in the full linear determinant model

For a finite field F with exact unit-group two-part 2^m, m at least one,
the full determinant level m contains an element outside the actual
predecessor level m-1. At m=1 it is an involution. At m at least two its
square generates the center of the full determinant level, as an equality
of subgroups of that level itself.

For m=1 choose the coordinate-swap matrix, whose determinant is -1 and
whose square is one; divisibility by two forces odd characteristic. For
m at least two choose a primitive 2^m-th root of unity ζ and multiply
diag(ζ,1) by the coordinate swap. Its determinant is -ζ, so it lies outside
the predecessor since 2^(m-1) is even and ζ has exact order 2^m. Its square
is the scalar matrix ζI. The common-center theorem for the top two levels
identifies their center with exactly those scalar roots, and primitive
root generation gives the required cyclic subgroup equality.

Source: Alperin--Brauer--Gorenstein II.3 Proposition 3, article p26,
using the actual linear determinant models of II.2 Lemma 1, article p17.
No Sylow recognition is assumed, and the endpoint m=1 is retained for the
semidihedral branch of the model comparison.
-/

namespace ABG
open Matrix.GeneralLinearGroup

/-- The full determinant level has an actual exterior involution at level
one, or an exterior element whose square generates its center at higher levels. -/
public theorem exists_linear_model_exterior
    (F : Type*) [Field F] [Finite F] (m : ℕ) (hm : 1 ≤ m)
    (hd : 2 ^ m ∣ Nat.card F - 1)
    (ho : Odd ((Nat.card F - 1) / 2 ^ m)) :
    ∃ a : determinantTwoPower F m,
      a.val ∉ determinantTwoPower F (m - 1) ∧
      ((m = 1 ∧ a ^ 2 = 1) ∨
        (2 ≤ m ∧ Subgroup.zpowers (a ^ 2) = Subgroup.center (determinantTwoPower F m))) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have heven : Even (2 ^ m) := Nat.even_pow.mpr ⟨by decide, by omega⟩
  by_cases hm1 : m = 1
  · subst m
    have h2 : 2 ∣ Nat.card F - 1 := by simpa using hd
    have hchar : ringChar F ≠ 2 := by
      intro h
      have hcard := FiniteField.even_card_of_char_two h
      rw [← Nat.card_eq_fintype_card] at hcard
      have hp : 0 < Nat.card F := Nat.card_pos
      omega
    have hs : coordinateSwap F ∈ determinantTwoPower F 1 := by
      rw [mem_determinantTwoPower, coordinateSwap_det, pow_one]
      simp
    refine ⟨⟨coordinateSwap F, hs⟩, ?_, Or.inl ⟨rfl, ?_⟩⟩
    · intro h
      have hh : (-1 : Fˣ) = 1 := by
        simpa only [Nat.sub_self, mem_determinantTwoPower, pow_zero, pow_one, coordinateSwap_det] using h
      exact Ring.neg_one_ne_one_of_char_ne_two hchar (congrArg Units.val hh)
    · apply Subtype.ext
      exact coordinateSwap_sq F
  · have hm2 : 2 ≤ m := by omega
    let U := rootsOfUnity (2 ^ m) F
    obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := U)
    let ζ : Fˣ := u.val
    have hord : orderOf ζ = 2 ^ m := by
      rw [show orderOf ζ = orderOf u from Subgroup.orderOf_coe u, hu]
      exact FiniteField.card_rootsOfUnity_of_dvd F _ hd
    have hpow : ζ ^ (2 ^ m) = 1 := by rw [← hord]; exact pow_orderOf_eq_one ζ
    let A := diagonalPair F (ζ, 1) * coordinateSwap F
    have hdet : det A = -ζ := diagonalPair_coordinateSwap_det F ζ
    have hA : A ∈ determinantTwoPower F m := by
      rw [mem_determinantTwoPower, hdet, heven.neg_pow, hpow]
    have hout : A ∉ determinantTwoPower F (m - 1) := by
      intro hh
      have hp : ζ ^ (2 ^ (m - 1)) = 1 := by
        have he : Even (2 ^ (m - 1)) := Nat.even_pow.mpr ⟨by decide, by omega⟩
        simpa only [mem_determinantTwoPower, hdet, he.neg_pow] using hh
      have hhdiv := orderOf_dvd_of_pow_eq_one hp
      rw [hord] at hhdiv
      have := Nat.le_of_dvd (by positivity : 0 < 2 ^ (m - 1)) hhdiv
      have hlt : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by decide) (by omega)
      omega
    refine ⟨⟨A, hA⟩, hout, Or.inr ⟨hm2, ?_⟩⟩
    apply Subgroup.map_injective (determinantTwoPower F m).subtype_injective
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (A ^ 2) = _
    rw [diagonalPair_coordinateSwap_sq]
    have hpred : m - 1 + 1 = m := Nat.sub_add_cancel hm
    rw [(top_determinant_central_layer F m hm hd ho).1,
      center_determinantTwoPower_map, hpred]
    rw [← (IsPrimitiveRoot.iff_orderOf.mpr hord).zpowers_eq, MonoidHom.map_zpowers]
end ABG
