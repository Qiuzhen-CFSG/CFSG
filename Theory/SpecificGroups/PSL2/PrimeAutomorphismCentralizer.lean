module

public import Theory.SpecificGroups.PSL2.PrimeCardInnerIndex
public import Theory.SpecificGroups.PGL2.NoncommutativeCentralizer

/-!
# Prime-field automorphism centralizers

The actual projective-linear conjugation map covers Aut(PSL₂(p)) for a
prime p greater than three. Transport the PGL₂ matrix-centralizer theorem
through that bijective map and a supplied PSL₂ model. Consequently the
centralizer of any noncommutative automorphism subgroup has exponent at
most two; the subgroup need not consist of inner automorphisms.

Source: Aschbacher–Smith, proof of 2.5.21, printed p.567, with prime-field
coverage from the existing semilinear automorphism calculation.
-/

public section

open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

/-- In the full automorphism group of a prime-field PSL₂ model, the centralizer
of a noncommutative subgroup has exponent at most two. -/
theorem prime_automorphism_centralizer_square
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    {Q : Type*} [Group Q] (eQ : Q ≃* PSL(2, ZMod p))
    (D : Subgroup (MulAut Q)) (hD : ¬ IsMulCommutative D)
    {a : MulAut Q} (ha : a ∈ centralizer (D : Set (MulAut Q))) : a ^ 2 = 1 := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  let hF : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, Fact.out, hodd, by decide, by simp⟩
  let hc : 3 < Nat.card (ZMod p) := by simpa using hp
  let eA : PGL2 (ZMod p) ≃* MulAut PSL(2, ZMod p) :=
    MulEquiv.ofBijective (pgl2InnerAutPSL2 (ZMod p) hF hc)
      ⟨pgl2InnerAutPSL2_injective (ZMod p) hF hc,
        prime_card_pgl_coverage (p := p) (ZMod p) (by simp) hF hc⟩
  exact Theory.PGL2.centralizer_square_eq_one_of_model
    ((MulAut.congr eQ).trans eA.symm) D hD ha

end Theory.PSL2

end
