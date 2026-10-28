module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Theory.Representation.CentralInvolutionFaithful
public import Theory.SpecificGroups.SL2.NormalMonolith

/-!
# Faithful irreducible factors for odd-characteristic SL2

A finite-dimensional faithful representation of `SL(2,p^m)` over `GF(p)`,
where `p` is odd and `m` is nonzero, contains a faithful irreducible
subrepresentation. In particular it has a faithful irreducible composition
factor of dimension at most that of the original representation.

The central matrix `-I` is a nonidentity involution, and every nontrivial
normal subgroup of SL2 contains it, including when `p^m = 3`. Apply the
central-involution extraction theorem to the minus eigenspace of `-I`.
The argument applies to reducible and nonsemisimple representations.

This proves the reduction implicit in Alperin--Brauer--Gorenstein II.4,
Lemma 18 (article p.45), whose proof invokes the irreducible classification
in Fong--Wong (1E) for an arbitrary faithful representation. The conclusion
records an actual subrepresentation, which is stronger than merely a factor.
-/

namespace Representation.SL2

private theorem two_ne_zero_of_odd_char
    {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] (hp : Odd p) :
    (2 : F) ≠ 0 := by
  intro h
  have hd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp h
  have hp2 : p = 2 := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
    (Fact.out : p.Prime).ne_one
  subst p
  exact (Nat.not_even_iff_odd.mpr hp) (by decide)

/-- A faithful defining-characteristic representation of odd SL2 contains a
faithful irreducible submodule, and therefore a faithful composition factor. -/
public theorem exists_faithful_irreducible_factor_of_sl2_faithful
    {p m : ℕ} [Fact p.Prime] (hp : Odd p) (_hm : m ≠ 0)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V]
    (rho : Representation (ZMod p)
      (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p m)) V)
    (hrho : Function.Injective rho) :
    ∃ W : Subrepresentation rho, IsIrreducible W.toRepresentation ∧
      Function.Injective W.toRepresentation ∧
      Module.finrank (ZMod p) W.toSubmodule ≤ Module.finrank (ZMod p) V := by
  have hchar := two_ne_zero_of_odd_char (F := ZMod p) hp
  have hfield := two_ne_zero_of_odd_char (F := GaloisField p m) hp
  apply exists_faithful_irreducible_subrepresentation hchar rho hrho (-1)
  · apply Subgroup.mem_center_iff.mpr
    intro g
    simp
  · exact neg_one_sq
  · intro h
    have hh := congrArg
      (fun g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField p m) =>
        (g : Matrix (Fin 2) (Fin 2) (GaloisField p m)) 0 0) h
    have heq : (-1 : GaloisField p m) = 1 := by simpa using hh
    apply hfield
    linear_combination -heq
  · intro N hN hneg
    let : N.Normal := hN
    exact Matrix.SpecialLinearGroup.eq_bot_of_neg_one_not_mem hfield N hneg

end Representation.SL2
