module
public import Stellmacher.SectionsOneToFourDefs
/-!
# Equivariant module equivalences preserve offender joins

For a fixed acting group X and subgroup S, an equivariant multiplicative
equivalence between finite modules V and W identifies the action-defined
Section One offender joins J(V,S) and J(W,S).

The equivalence restricts to a bijection on the fixed subgroup of every
actor subgroup. It therefore preserves both cardinalities in the Section
One measure. The elementary-abelian offender conditions are unchanged,
so the defining offender families, and hence their generated joins, agree.

This is the module-presentation step in comparing the canonical Section Six
quotient with an ambient quotient-module witness, as needed for Stellmacher
(6.4) and (8.4), Journal of Algebra 190 (1997), pp.31–32 and38.
Source: definitions of m, oneA and oneJ in refs/latex/stellmacher-n-group.tex.
-/

namespace Stellmacher.SectionOne
universe u

public theorem oneJ_eq_of_module_equiv
    {X V W : Type u} [Group X] [Group V] [Group W] [Finite V] [Finite W]
    [MulDistribMulAction X V] [MulDistribMulAction X W]
    (e : V ≃* W) (he : ∀ (a : X) (v : V), e (a • v) = a • e v)
    (S : Subgroup X) : oneJ (V := V) S = oneJ (V := W) S := by
  have hcard (A : Subgroup X) :
      Nat.card (FixedPoints.subgroup A V) = Nat.card (FixedPoints.subgroup A W) := by
    have hfix (v : V) : v ∈ FixedPoints.subgroup A V ↔ e v ∈ FixedPoints.subgroup A W := by
      simp only [FixedPoints.mem_subgroup]
      constructor
      · intro hv a
        change (a : X) • e v = e v
        rw [← he]
        exact congrArg e (hv a)
      · intro hv a
        apply e.injective
        change e ((a : X) • v) = e v
        rw [he]
        exact hv a
    exact Nat.card_congr (Equiv.subtypeEquiv e.toEquiv hfix)
  have hVcard : Nat.card V = Nat.card W := Nat.card_congr e.toEquiv
  unfold oneJ
  congr 1
  ext A
  simp only [Set.mem_ofPred_eq,oneA,m,hVcard,hcard]
end Stellmacher.SectionOne
