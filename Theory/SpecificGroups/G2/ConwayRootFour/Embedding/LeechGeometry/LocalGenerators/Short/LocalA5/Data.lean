module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.Factors
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.Scalar

/-!
# The actual local A₅ and its two factor actions

This contract separates two missing source arguments. The geometric argument
must construct the A₅ centralizing the relevant D₁₀ in the literal Leech
quotient, and identify its two faithful SL₂(4) projections. Their comparison
is the automorphism `twist`. The common reflection and cubic torus specify
its restriction to S₃; this restriction alone does not determine `twist`.

The separate identification must prove that `twist` fixes the upper shear.
Then the existing scalar marking gives the precise seed consumed by
`Short.nonempty_shortFrame_of_scalar_seed`. No inhabitant of this contract,
canonical long frame, or centralizer faithfulness is asserted.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
using 47.2 and 48.8. The source's asserted diagonal uniqueness needs an
additional ambient argument; `DiagonalAmbiguity` records the linear issue.
-/

@[expose] public noncomputable section
open Atlas.Conway
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5

/-- A local SL₂(4) in the actual quotient, with both factor projections and
the scalar conjugacy class. There is no prescribed short-root action here. -/
structure Data (L : LongFrame) where
  twist : MulAut (SL(2,F))
  lift : SL(2,F) →* LeechCentralQuotient
  lift_mem : ∀ a, lift a ∈ centralizerI
  on_action : ∀ a v,
    quotientModTwoRepresentation (lift a) (L.coordinates v) =
      L.coordinates (pairRepresentation (a, twist a) v)
  twist_flip : twist flip = flip
  twist_torus : ∀ t : Fˣ, twist (torus t) = (torus t)⁻¹
  scalar_class : IsConj (lift shear) scalarInvolution

/-- The factor action makes this an embedding, independently of faithfulness
of the entire centralizer on the fixed space. -/
theorem Data.lift_injective {L : LongFrame} (D : Data L) : Function.Injective D.lift := by
  intro a b h
  have he : pairRepresentation (a, D.twist a) = pairRepresentation (b, D.twist b) := by
    apply LinearEquiv.ext
    intro v
    apply L.coordinates_injective
    rw [← D.on_action, ← D.on_action, h]
  exact congrArg Prod.fst (pairRepresentation_injective he)

/-- Consumer of the separate diagonal identification. This is conditional;
the construction and the shear identity still require their own proofs. -/
theorem Data.scalar_short_seed_of_twist_shear {L : LongFrame} (D : Data L)
    (h : D.twist shear = shear) :
    ∃ g ∈ centralizerI, L.Intertwines g (Atlas.G2.rootC 1) ∧
      IsConj g scalarInvolution := by
  refine ⟨D.lift shear, D.lift_mem shear, ?_, D.scalar_class⟩
  intro v
  rw [D.on_action, h, shear_action]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5
