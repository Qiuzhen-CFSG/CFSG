/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianMonomialFaithfulness.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianMonomialEmbedding
public import Theory.AtlasPort.Janko2.Conway.IcosianMonomialKernel

/-!
# IcosianMonomialFaithfulness

The monomial representation is faithful. Evaluation on single-coordinate vectors
recovers its permutation and unit coefficients, hence the image order.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianMonomialFaithfulness.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Lattices

theorem icosianMonomialRepresentation_injective :
    Function.Injective icosianMonomialRepresentation := by
  intro g h he
  have hp (i : Fin 3) : g.right.symm i=h.right.symm i := by
    by_contra hne
    have hv := congrArg (fun f : IcosianRationalCoordinates ≃ₗ[ℚ] IcosianRationalCoordinates =>
      f (Pi.single (g.right.symm i) (1 : IcosianQuaternion)) i) he
    have hz : (icosianMonomialUnits (g.left i) : IcosianQuaternion)=0 := by
      simp [icosianMonomialRepresentation,icosianMonomialLinear,Ne.symm hne] at hv
    exact (Units.ne_zero (icosianMonomialUnits (g.left i))) hz
  apply SemidirectProduct.ext
  · funext i
    apply icosianNormOne_value_injective
    have hv := congrArg (fun f : IcosianRationalCoordinates ≃ₗ[ℚ] IcosianRationalCoordinates =>
      f (Pi.single (g.right.symm i) (1 : IcosianQuaternion)) i) he
    simpa [icosianMonomialRepresentation,icosianMonomialLinear,icosianMonomialUnits,
      Pi.single_apply,← hp i] using hv
  · have hsymm : g.right.symm=h.right.symm := Equiv.ext hp
    simpa using congrArg Equiv.symm hsymm

theorem icosianMonomialToHermitian_injective : Function.Injective icosianMonomialToHermitian := by
  intro g h he
  apply Subtype.ext
  apply icosianMonomialRepresentation_injective
  exact congrArg Subtype.val he

theorem icosianMonomialToHermitian_range_card : Nat.card icosianMonomialToHermitian.range=2304 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective icosianMonomialToHermitian_injective).toEquiv]
  exact icosianLiftedMonomial_card

end Atlas.Conway
