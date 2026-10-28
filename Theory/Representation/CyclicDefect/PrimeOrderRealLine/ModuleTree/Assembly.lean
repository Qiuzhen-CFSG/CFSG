module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.Contracts
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.Graph

/-!
# Assembly of the actual modules into a Brauer tree

The decomposition numbers of the supplied simple modules are the zero-one
incidence matrix of a connected graph. The vertex count proves that this
is a genuine tree, including injectivity of its unordered edge pairs.
Summing a projective column leaves exactly its two ordinary endpoints, so
both regular-character identities use the original modules and root lift.

This is a conditional assembly of Feit I.17.8--9 and VII.2.13--15, VII.6.4.
The existence of decomposition modules and cyclic incidence remains with
their respective source-theorem producers.
-/

public section
noncomputable section
open scoped BigOperators Classical

namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree
open ModularBlock.PrimeBlockConstruction

variable {p : ℕ} {G : Type*} [Group G] [Finite G]
    {K : Type*} [Field K] {m n : ℕ}
    {d : PrimeCongruenceBlockData p G}
    {residue : Localization.AtPrime d.primeIdeal →+* K}
    {L : CyclicRootLift K m} {a : Decomposition d residue L n}

/-- A projective column is the sum of exactly its two ordinary endpoints. -/
theorem Incidence.column_character (c : Incidence a) (e : Fin n) (g : G) :
    (∑ v : {i // i ∈ d.block},
      (a.multiplicity v e : ℂ) * d.chi v.val (ConjClasses.mk g)) =
      d.chi (c.left e).val (ConjClasses.mk g) +
        d.chi (c.right e).val (ConjClasses.mk g) := by
  have hterm (v : {i // i ∈ d.block}) :
      (a.multiplicity v e : ℂ) * d.chi v.val (ConjClasses.mk g) =
        (if v = c.left e then d.chi v.val (ConjClasses.mk g) else 0) +
        (if v = c.right e then d.chi v.val (ConjClasses.mk g) else 0) := by
    rw [c.multiplicity_eq]
    by_cases hl : v = c.left e
    · subst v
      simp [c.endpoints_ne e]
    · by_cases hr : v = c.right e
      · subst v
        simp [(c.endpoints_ne e).symm]
      · simp [hl, hr]
  simp_rw [hterm, Finset.sum_add_distrib]
  simp

/-- Combine actual decomposition modules and connected cyclic incidence. -/
def Incidence.toTree (c : Incidence a) (hcard : d.block.card = n + 1) :
    Tree d.chi d.block p n L := by
  have hgraph := endpointGraph_tree_of_connected c.left c.right c.endpoints_ne
    c.connected (by simpa using hcard)
  refine {
    left := c.left
    right := c.right
    endpoints_ne := c.endpoints_ne
    edges_injective := hgraph.1
    isTree := hgraph.2
    degree := a.degree
    rep := a.rep
    irreducible := a.irreducible
    inequivalent := a.inequivalent
    decomposition := ?_
    projective := ?_ }
  · intro g hg v
    rw [a.restriction g hg v]
    apply Finset.sum_congr rfl
    intro e _
    rw [c.multiplicity_eq]
    split_ifs <;> simp
  · intro e
    exact {
      degree := (a.projective e).degree
      rep := (a.projective e).rep
      projective := (a.projective e).projective
      character_eq := fun g hg => ((a.projective e).character_eq g hg).trans
        (c.column_character e g) }

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree
