module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.FixedDimension
public import Theory.SpecificGroups.Alternating.FiveInvolutionFusion

/-!
# A fixed scalar involution for the short-root marking

The double transposition (01)(23) in the actual scalar A₅ lies in the
published U. It has order two and an actual Leech lift squaring to central
negation. The single involution class in A₅ reduces marking every scalar
involution to marking this one element.

This records the concrete intermediate for the root-four fusion used in
Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284, with the
root-four conventions on p.269. It does not identify the chosen scalar with
`markedInvolution`: that still requires actual conjugacy in the Leech
central quotient. In particular, the square calculation is not used as a
substitute for this conjugacy. The consumer is `LocalGenerators.Short`.
-/

open Atlas.Conway Atlas.Lattices Equiv
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators

/-- The fixed double transposition in the five-point scalar model. -/
def scalarModelInvolution : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

theorem scalarModelInvolution_order : orderOf scalarModelInvolution = 2 :=
  orderOf_eq_prime (by decide) (by decide)

/-- Its image under the literal scalar embedding, not an abstract class tag. -/
def scalarInvolution : LeechCentralQuotient := scalarFive scalarModelInvolution

theorem scalarInvolution_order : orderOf scalarInvolution = 2 := by
  rw [scalarInvolution, orderOf_injective scalarFive scalarFive_injective]
  exact scalarModelInvolution_order

/-- Every scalar involution is conjugate to the chosen one in the actual quotient. -/
theorem scalarFive_involution_isConj (s : alternatingGroup (Fin 5))
    (hs : orderOf s = 2) : IsConj (scalarFive s) scalarInvolution :=
  scalarFive.map_isConj
    (alternatingGroup.five_involutions_isConj s scalarModelInvolution hs
      scalarModelInvolution_order)

/-- The order-four lift exists independently of the still-needed marking. -/
theorem scalarInvolution_lift :
    ∃ g : LeechIsometryGroup, leechCentralProjection g = scalarInvolution ∧
      g ^ 2 = negationIsometry :=
  scalarFive_involution_lift scalarModelInvolution (by decide) (by decide)

/-- The chosen element belongs to the literal published four-group. -/
theorem scalarInvolution_mem_U : scalarInvolution ∈ U := by
  let p : alternatingGroup fourPoints :=
    ⟨Equiv.swap (⟨0, by decide⟩ : fourPoints) ⟨1, by decide⟩ *
      Equiv.swap (⟨2, by decide⟩ : fourPoints) ⟨3, by decide⟩, by
        rw [Equiv.Perm.mem_alternatingGroup]
        decide⟩
  refine ⟨p, ?_, ?_⟩
  · apply Subgroup.subset_closure
    decide
  · change scalarFive (alternatingGroup.ofSubtype fourPoints p) =
      scalarFive scalarModelInvolution
    congr 1
    decide

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators
