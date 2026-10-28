module

public import Theory.Representation.PSL3Two.NaturalOrbits
public import Theory.SpecificGroups.PSL3Two.Parabolics.Actions
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.SymmetricModels

/-!
# Stabilizers on the natural binary three-space

Transitivity transports the standard point parabolic to every nonzero vector.
Its faithful affine action identifies it with S₄. A subgroup of order twelve
in such a point stabilizer is therefore A₄, by the uniqueness of the index-two
subgroup of S₄. This is the stabilizer step for the rank-four central extension
in Aschbacher--Smith, 13.1.12, printed pp.872--873.
-/

public noncomputable section
open Subgroup
namespace BinaryLinearThree.OrbitStabilizers
open Matrix.PSL3Two

/-- The original natural point stabilizer, with its actual matrix action. -/
def natural (v : Vector) : Subgroup BinaryLinearThree.Group :=
  MulAction.stabilizer BinaryLinearThree.Group v

theorem mem_natural (g : BinaryLinearThree.Group) (v : Vector) :
    g ∈ natural v ↔ W g v = v := Iff.rfl

private theorem natural_standard : natural ![1,0,0] = pointParabolicSL := by
  rw [← Fano.stabilizer_flagPoint_SL]
  ext g
  change g • (![1,0,0] : Vector) = ![1,0,0] ↔ g • flagPoint = flagPoint
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- Every nonzero natural vector has symmetric-four stabilizer. -/
def naturalEquivSymmetric (v : Vector) (hv : v ≠ 0) :
    natural v ≃* Equiv.Perm (Fin 4) := by
  let h := natural_transitive_nonzero ![1,0,0] v (by decide) hv
  let g := Classical.choose h
  have hg := Classical.choose_spec h
  exact (MulAction.stabilizerEquivStabilizer (show v = g • (![1,0,0] : Vector)
    from hg.symm)).symm.trans
      ((MulEquiv.subgroupCongr natural_standard).trans MarkedAutomorphisms.pointEquivSymmetric)

/-- The order-twelve subgroup fixing a nonzero natural vector is A₄. -/
def twelveEquivAlternating (H : Subgroup BinaryLinearThree.Group)
    (v : Vector) (hv : v ≠ 0) (hH : H ≤ natural v) (hc : Nat.card H = 12) :
    H ≃* alternatingGroup (Fin 4) := by
  let e := naturalEquivSymmetric v hv
  let f : H →* Equiv.Perm (Fin 4) := e.toMonoidHom.comp (inclusion hH)
  have hi : Function.Injective f := e.injective.comp (inclusion_injective hH)
  have hr : Nat.card f.range = 12 :=
    (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm.trans hc
  have hindex : f.range.index = 2 := by
    have hh := f.range.card_mul_index
    rw [hr, Nat.card_perm, Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
    omega
  exact (MonoidHom.ofInjective hi).trans
    (MulEquiv.subgroupCongr (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex))

end BinaryLinearThree.OrbitStabilizers
