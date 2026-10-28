module

public import Theory.SpecificGroups.PSL3.StandardCubicFixedNine.Field
public import Theory.SpecificGroups.PSL3.StandardCubicFixedNine.Reduction
public import Theory.SpecificGroups.PSL3.StandardCubicFixedNine.Descent

/-!
# Fixed inner nine-groups for standard cubic automorphisms of PSL₃

The graph reduction puts a non-diagonal cubic actor into linear–field form
with a coefficient automorphism of order three. Projective semilinear
descent conjugates it to that coefficient automorphism: scalar norm lifting
first removes the projective obstruction, then matrix Hilbert–90 supplies
the conjugator. The pure-field construction transports an elementary inner
subgroup of order nine, pointwise fixed by the original actor.

All descent premises are discharged, including for mixed field–diagonal
actors. The degree-two case is covered by the field-of-order-four obstruction
in `Reduction`. Simplicity and nonsolvability are inherited model hypotheses;
neither a separate perfectness assumption nor positivity of the degree is
needed. The existing conditional assembly remains publicly available through
`Conditional`.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, A.3.16–18, printed pp.51–53,
and the final paragraph of 15.3.37, printed p.1135.
-/

public section

open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3.StandardCubicFixedNine
variable {F : Type*} [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

/-- A non-inner-diagonal standard automorphism of order three fixes an
elementary abelian inner subgroup of order nine. Projective descent is proved
on the actual matrix quotient, with no conjugacy or fixed-subgroup premise. -/
theorem exists_fixed_inner_nine
    (hns : ¬ Group.IsSolvable PSL(3,F)) {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : Even n)
    (a : MulAut PSL(3,F)) (ha : a ∈ standard F)
    (horder : orderOf a = 3) (hdiag : a ∉ innerDiagonal F) :
    ∃ E : Subgroup (MulAut PSL(3,F)), IsElementaryAbelian 3 E ∧
      E ≤ MulAut.innerSubgroup PSL(3,F) ∧ Nat.card E = 9 ∧
      E ≤ Subgroup.centralizer ({a} : Set (MulAut PSL(3,F))) := by
  exact exists_fixed_inner_nine_of_descent hns hF hn
    Descent.exists_conjugate_field a ha horder hdiag

end Matrix.PSL3.StandardCubicFixedNine
