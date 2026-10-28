module

public import Theory.Representation.OrthogonalFourPlusMatrix.InvolutionResidual.Preserving.Factors
public import Theory.Representation.OrthogonalFourPlusMatrix.InvolutionResidual.Preserving.ScalarCubic

/-!
# Nonsolvable centralizers of binary determinant-module involutions

A nonidentity involution normalizing the literal SL₂(4) × SL₂(4) action either
interchanges its two factor images or every nonsolvable subgroup centralizing
it contains an element of order three fixing only zero on the matrix space.

The proof uses the automorphism theorem for a centerless simple square and
solvability of proper A₅ subgroups. In the preserving case, a nonsolvable
pointwise fixed subgroup either contains a whole factor or forces both
coordinate automorphisms to be trivial. A whole factor supplies the cubic
actor; the second case makes the involution a scalar, hence the identity.
This handles inner and field automorphisms without assuming their matrix
normal forms or enumerating GL₈(2).

Source application: Aschbacher–Smith, Lemma 14.4.9, printed p.1010, the
interchange of the components in the exchanged orthogonal model. The source
consumer must still exclude the cubic alternative using its fixed-point counts.
-/

public section
namespace ClassicalOrthogonal.FourPlusMatrix.Binary.InvolutionResidual

/-- The finite normalizer dichotomy for the actual binary determinant action. -/
theorem swapsFactors_or_exists_cubic
    (t : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ Subgroup.normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)))
    (h2 : t ^ 2 = 1) (hne : t ≠ 1)
    (R : Subgroup G) (hn : ¬ Group.IsSolvable R)
    (hc : ∀ r : R, Commute t (linearAction (r : G))) :
    SwapsFactors t ∨
      ∃ r : R, orderOf r = 3 ∧ ∀ v : V, action (r : G) v = v → v = 0 := by
  rcases normalizer_factor_reduction t ht R hn hc with hswap | hcentral | hleft | hright
  · exact Or.inl hswap
  · exact (hne (centralizing_involution_eq_one t h2 hcentral)).elim
  · exact Or.inr (exists_cubic_of_factor_le R (Or.inl hleft))
  · exact Or.inr (exists_cubic_of_factor_le R (Or.inr hright))

end ClassicalOrthogonal.FourPlusMatrix.Binary.InvolutionResidual
