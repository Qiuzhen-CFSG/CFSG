module

public import Theory.Representation.BinaryTwoPowerDegree
public import Theory.SpecificGroups.SymplecticFour.Flag

/-!
# Two-power elements in symplectic four-space

Every element of two-power order in the literal symplectic group on four-space
has fourth power one over a field of characteristic two. Its natural action is
faithful, and the general dimension bound applies: subtracting the identity
gives a nilpotent endomorphism whose kernels stabilize by dimension four.
No finiteness assumption on the field is needed.

This supplies the exponent obstruction for the exceptional-group inspection
in Aschbacher–Smith, *The Classification of Quasithin Groups*, G.4.1, printed
p.342: a two-element with nonidentity fourth power cannot embed faithfully in
this symplectic carrier.
-/

public section
namespace Theory.SpecificGroups.SymplecticFour.TwoPower
variable {F : Type*} [Field F] [CharP F 2]

/-- Every two-power element of the native characteristic-two symplectic
four-space group has fourth power one. -/
theorem pow_four_eq_one_of_pow_two_pow_eq_one (g : Sp F) (k : ℕ)
    (hg : g ^ (2 ^ k) = 1) : g ^ 4 = 1 := by
  have hf : Function.Injective (Representation.symplecticNatural (k := F) 2) := by
    intro x y hxy
    apply Subtype.ext
    apply Matrix.toLin'.injective
    exact hxy
  exact Representation.BinaryTwoPowerDegree.pow_eq_one_of_finrank_le
    (Representation.symplecticNatural (k := F) 2) hf (m := 2) (by simp) g hg

end Theory.SpecificGroups.SymplecticFour.TwoPower
