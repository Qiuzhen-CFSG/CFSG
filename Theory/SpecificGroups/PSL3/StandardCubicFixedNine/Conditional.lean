module

public import Theory.SpecificGroups.PSL3.StandardCubicFixedNine.Field
public import Theory.SpecificGroups.PSL3.StandardCubicFixedNine.Reduction

/-!
# Assembling fixed inner nine-groups from projective descent

Graph elimination puts a non-diagonal cubic standard actor into linear–field
form with a coefficient automorphism of order three. Given projective
semilinear descent, transport the pure-field elementary inner nine-group
back to the original actor. The field of order four is excluded directly.

This shared module preserves the conditional assembly interface. The parent
`StandardCubicFixedNine` discharges its descent premise using `Descent`, whose
concrete consumer also uses the pure-field transport re-exported here.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, A.3.16–18, printed pp.51–53,
and the final paragraph of 15.3.37, printed p.1135.
-/

public section

open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3.StandardCubicFixedNine
variable {F : Type*} [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

/-- Conditional assembly: projective cubic descent is the only remaining
model premise. The caller must prove it on the actual projective quotient. -/
theorem exists_fixed_inner_nine_of_descent
    (hns : ¬ Group.IsSolvable PSL(3,F)) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : Even n)
    (descent : ∀ (m : GL (Fin 3) F) (σ : F ≃+* F), orderOf σ = 3 →
      (linearConj F m * fieldAction F σ) ^ 3 = 1 →
      ∃ d : MulAut PSL(3,F),
        MulAut.congr d (linearConj F m * fieldAction F σ) = fieldAction F σ)
    (a : MulAut PSL(3,F)) (ha : a ∈ standard F)
    (horder : orderOf a = 3) (hdiag : a ∉ innerDiagonal F) :
    ∃ E : Subgroup (MulAut PSL(3,F)), IsElementaryAbelian 3 E ∧
      E ≤ MulAut.innerSubgroup PSL(3,F) ∧ Nat.card E = 9 ∧
      E ≤ Subgroup.centralizer ({a} : Set (MulAut PSL(3,F))) := by
  classical
  have ha3 : a ^ 3 = 1 := (orderOf_eq_prime_iff.mp horder).1
  by_cases hfour : Nat.card F = 2 ^ 2
  · exact (hdiag (cubic_innerDiagonal_of_card_four hfour a ha ha3)).elim
  · let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    obtain ⟨m, σ, he, hs⟩ := cubic_factorization a ha ha3 hdiag
    obtain ⟨d, hd⟩ := descent m σ hs (he ▸ ha3)
    apply exists_fixed_inner_nine_of_conjugate_field hns hF hn a d σ
      (orderOf_eq_prime_iff.mp hs).1
    rwa [he]

end Matrix.PSL3.StandardCubicFixedNine
