module

public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.Action

/-!
# Assembly of the McLaughlin carrier comparison from generator lifts

The two marked generator lifts give an injective homomorphism from the exact
ATLAS permutation carrier into the Leech triangle stabilizer. A lower bound
of 898128000 for the permutation carrier makes that homomorphism surjective,
since the Leech model has this proved order. The resulting multiplicative
isomorphism is equivariant for the original degree-275 permutation action.

The final application retains the literal source map
`E → E/Z(E) → Carrier → Model` and proves its kernel is the original center.
This is the model comparison required for Aschbacher–Smith A.2.19 (printed
pp.40–41) and I.1.4(2) (printed p.408).

Both additional premises remain explicit: `qt-i01-mcl-generator-lifts`
constructs the generator lifts, and `qt-i01-mcl-permutation-order-lower`
certifies the permutation order lower bound. `qt-i01-mcl-carrier-comparison`
retains their final assembly into the unconditional `permutationModelEquiv`.
No full graph automorphism group identification is asserted or used.
-/

@[expose] public section
noncomputable section

namespace Theory.SpecificGroups.McLaughlin.Multiplier

open Atlas.Sporadic.McLaughlin (Model Points)
open Sporadic.LeechRelated.McL
open PerfectCentralCovering

namespace ModelComparison

/-- The independent permutation order bound makes the faithful lift surjective. -/
theorem carrierEmbedding_bijective (d : GeneratorLifts)
    (hcard : 898128000 ≤ Nat.card Carrier) : Function.Bijective d.carrierEmbedding := by
  apply d.carrierEmbedding_injective.bijective_of_nat_card_le
  simpa only [Atlas.Sporadic.McLaughlin.card, Atlas.Sporadic.McLaughlin.order] using hcard

/-- The Leech action image is precisely the generated permutation group. -/
theorem generated_eq_range (d : GeneratorLifts)
    (hcard : 898128000 ≤ Nat.card Carrier) :
    generated = (labelledAction d.pointEquiv).range := by
  apply Subgroup.eq_of_le_of_card_ge d.generated_le_range
  have hc := Nat.card_congr (MonoidHom.ofInjective
    (labelledAction_injective d.pointEquiv)).toEquiv
  rw [← hc, Atlas.Sporadic.McLaughlin.card]
  exact hcard

end ModelComparison

open ModelComparison

/-- Conditional assembly from concrete generator lifts and the independent
permutation order lower bound. This does not supply either premise. -/
def permutationModelEquivOfLifts (d : GeneratorLifts)
    (hcard : 898128000 ≤ Nat.card Carrier) : Carrier ≃* Model :=
  MulEquiv.ofBijective d.carrierEmbedding (carrierEmbedding_bijective d hcard)

/-- The isomorphism retains every original permutation action. -/
theorem permutationModelEquivOfLifts_apply (d : GeneratorLifts)
    (hcard : 898128000 ≤ Nat.card Carrier) (g : Carrier) (x : Fin 275) :
    permutationModelEquivOfLifts d hcard g • d.pointEquiv x =
      d.pointEquiv (g.val x) := d.carrierEmbedding_apply g x

/-- The first generator maps to the specified Leech isometry itself. -/
theorem permutationModelEquivOfLifts_generatorA (d : GeneratorLifts)
    (hcard : 898128000 ≤ Nat.card Carrier) :
    permutationModelEquivOfLifts d hcard
      ⟨generatorA, Subgroup.subset_closure (by simp)⟩ = d.liftA := by
  apply labelledAction_injective d.pointEquiv
  exact (d.labelledAction_carrierEmbedding _).trans d.labelledAction_liftA.symm

/-- The second generator maps to the specified Leech isometry itself. -/
theorem permutationModelEquivOfLifts_generatorB (d : GeneratorLifts)
    (hcard : 898128000 ≤ Nat.card Carrier) :
    permutationModelEquivOfLifts d hcard
      ⟨generatorB, Subgroup.subset_closure (by simp)⟩ = d.liftB := by
  apply labelledAction_injective d.pointEquiv
  exact (d.labelledAction_carrierEmbedding _).trans d.labelledAction_liftB.symm

variable {E : Type*} [Group E] [Group.IsPerfect E]

/-- The actual source central quotient followed by the constructed comparison. -/
def sourceCoverOfGeneratorLifts (d : GeneratorLifts)
    (hcard : 898128000 ≤ Nat.card Carrier)
    (e : E ⧸ Subgroup.center E ≃* Carrier) : Cover E Model :=
  sourceCover (e.trans (permutationModelEquivOfLifts d hcard))

/-- Compatibility with the literal quotient projection used by A.2.19. -/
theorem sourceCoverOfGeneratorLifts_apply (d : GeneratorLifts)
    (hcard : 898128000 ≤ Nat.card Carrier)
    (e : E ⧸ Subgroup.center E ≃* Carrier) (g : E) :
    (sourceCoverOfGeneratorLifts d hcard e).toMonoidHom g =
      permutationModelEquivOfLifts d hcard (e (QuotientGroup.mk g)) := rfl

/-- The comparison does not change the kernel of the source quotient map. -/
theorem sourceCoverOfGeneratorLifts_kernel (d : GeneratorLifts)
    (hcard : 898128000 ≤ Nat.card Carrier)
    (e : E ⧸ Subgroup.center E ≃* Carrier) :
    (sourceCoverOfGeneratorLifts d hcard e).toMonoidHom.ker = Subgroup.center E :=
  sourceCover_kernel (e.trans (permutationModelEquivOfLifts d hcard))

/-- The source quotient action and the Leech action agree under the marked
labelling, for the original source element and quotient equivalence. -/
theorem sourceCoverOfGeneratorLifts_action (d : GeneratorLifts)
    (hcard : 898128000 ≤ Nat.card Carrier)
    (e : E ⧸ Subgroup.center E ≃* Carrier) (g : E) (x : Fin 275) :
    (sourceCoverOfGeneratorLifts d hcard e).toMonoidHom g • d.pointEquiv x =
      d.pointEquiv ((e (QuotientGroup.mk g)).val x) :=
  permutationModelEquivOfLifts_apply d hcard (e (QuotientGroup.mk g)) x

end Theory.SpecificGroups.McLaughlin.Multiplier
