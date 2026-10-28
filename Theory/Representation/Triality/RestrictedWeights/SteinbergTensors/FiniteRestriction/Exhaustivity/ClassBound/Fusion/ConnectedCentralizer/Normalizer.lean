module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Reduction
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusData
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Normalizer.Characters

/-!
# Lifting D4 torus stabilizers into the centralizing root groups

A weight-one root and its negative both centralize the torus point. Thus every
reflection representative supported on its two root groups belongs to the
proposed connected subgroup. If these reflections generate the Weyl stabilizer,
any centralizing normalizer element differs from their product by an element
of the torus, proving the desired containment.

The actual normalizer action, root-group lifts, toral kernel and stabilizer
generation remain explicit inputs. This module supplies their conditional
assembly, not an unconditional normalizer or connectedness theorem.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 4.10', 5.3, 6.4(b),
8.2(4)--(7), and 8.3(c).
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ConnectedCentralizer.Normalizer
universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Both opposite root groups centralize the same torus points. -/
theorem neg_rootWeight_eq_one (S : Geometry K)
    (t : Variety.Point S.torus.carrierVariety) (a : S.roots.Root)
    (ha : (S.roots.rootWeight a).pointCharacter t = 1) :
    (S.roots.rootWeight (S.roots.neg a)).pointCharacter t = 1 := by
  rw [S.realized.2.2.2.1 a]
  change ((torusPointEval S.torus.carrierVariety t
    (S.roots.rootWeight a)⁻¹) : k) = 1
  rw [map_inv, Units.val_inv_eq_inv_val]
  change ((S.roots.rootWeight a).pointCharacter t)⁻¹ = 1
  rw [ha, inv_one]

/-- A pair of opposite root groups of weight one belongs to the proposed
connected subgroup. -/
theorem opposite_rootSubgroups_le (S : Geometry K)
    (t : Variety.Point S.torus.carrierVariety) (a : S.roots.Root)
    (ha : (S.roots.rootWeight a).pointCharacter t = 1) :
    (S.roots.rootSubgroup a).toSubgroup ⊔
      (S.roots.rootSubgroup (S.roots.neg a)).toSubgroup ≤ toralRootSubgroup S t := by
  apply sup_le
  · exact (rootSubgroup_le_RootSubgroupGenerated S.roots ha).trans le_sup_right
  · exact (rootSubgroup_le_RootSubgroupGenerated S.roots
      (neg_rootWeight_eq_one S t a ha)).trans le_sup_right

/-- A centralizing normalizer element has Weyl class fixing the torus point. -/
theorem Realization.mem_stabilizer {S : Geometry K} {n : ℕ}
    {D : AmbientCount.TorusData S n} (R : Realization S D)
    (t : Variety.Point S.torus.carrierVariety) (g : S.torus.normalizer.toSubgroup)
    (hg : (g : Variety.Point K) ∈ Subgroup.centralizer {S.torus.includePoint t}) :
    let := D.action
    R.toWeyl g ∈ MulAction.stabilizer AmbientCount.Weyl t := by
  let := D.action
  change R.toWeyl g • t = t
  apply S.torus.inclusion_injective
  change S.torus.includePoint (R.toWeyl g • t) = S.torus.includePoint t
  rw [R.conjugation, Subgroup.mem_centralizer_singleton_iff.mp hg]
  group

/-- Lift the reflection subgroup through the normalizer using actual opposite
root-group representatives. -/
theorem Realization.reflections_le_map {S : Geometry K} {n : ℕ}
    {D : AmbientCount.TorusData S n} (R : Realization S D)
    (t : Variety.Point S.torus.carrierVariety) :
    toralReflectionSubgroup S t ≤
      ((toralRootSubgroup S t).comap S.torus.normalizer.toSubgroup.subtype).map
        R.toWeyl := by
  apply (Subgroup.closure_le _).mpr
  rintro w ⟨a, ha, rfl⟩
  obtain ⟨g, hg, hroot⟩ := R.reflection_lift a
  exact ⟨g, opposite_rootSubgroups_le S t a ha hroot, hg⟩

/-- Conditional assembly of the normalizer inclusion. The two geometric
obligations are explicit; this theorem does not assert their existence. -/
theorem toralNormalizerCentralizer_le_of_realization_of_reflectionGeneration
    (S : Geometry K) {n : ℕ} (D : AmbientCount.TorusData S n)
    (t : Variety.Point S.torus.carrierVariety)
    (R : Realization S D) (hgen : ReflectionGeneration D t) :
    toralNormalizerCentralizer S t ≤ toralRootSubgroup S t := by
  intro g hg
  let gN : S.torus.normalizer.toSubgroup := ⟨g, hg.1⟩
  have hw : R.toWeyl gN ∈ toralReflectionSubgroup S t :=
    hgen (R.mem_stabilizer t gN hg.2)
  obtain ⟨r, hr, heq⟩ := R.reflections_le_map t hw
  have hker : R.toWeyl (gN * r⁻¹) = 1 := by
    rw [map_mul, map_inv, heq, mul_inv_cancel]
  have htoral : ((gN * r⁻¹ : S.torus.normalizer.toSubgroup) : Variety.Point K) ∈
      toralRootSubgroup S t :=
    (show S.torus.toSubgroup ≤ toralRootSubgroup S t from le_sup_left)
      (R.ker_le (gN * r⁻¹) hker)
  have hmul := (toralRootSubgroup S t).mul_mem htoral hr
  change g * (r : Variety.Point K)⁻¹ * (r : Variety.Point K) ∈
    toralRootSubgroup S t at hmul
  simpa only [inv_mul_cancel_right] using hmul

end ConnectedCentralizer.Normalizer
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
