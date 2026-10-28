module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.Homology

/-!
# A distinguished orbit in the canonical homology module

The binary column below is fixed by the literal involution a. A fixed dual
row pairs to one with it and annihilates im(a - 1), proving that its homology
class is nonzero. The local word subgroup acts on this class; we define its
actual orbit and the group of linear automorphisms preserving that orbit.

The local image preserves the orbit by its definition. For the entire
involution centralizer, preservation is a separate mathematical obligation.
No orbit size, dimension, stabilizer order or whole-centralizer preservation
is asserted here. In particular, the quotient is not identified with Q/Z(Q).
All vector certificates use a and left column action directly.

Source motivation: GLS3, Table 5.3i, printed p.270. The source matrices and
ATLAS attribution are in Model.Data and TwoCoreCentralizer/source/README.md.
The exploratory orbit and sum-graph calculations are recorded in
ImageBound/source/; these supply witnesses, not proof premises.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation

/-- A fixed column, specified in the original 112-dimensional basis. -/
def distinguishedVector : NaturalModule :=
  fun i => if (15988596176158495 : ℕ).testBit i.val then 1 else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem distinguishedVector_fixed : displacement distinguishedVector = 0 := by
  rw [displacement_apply, sub_eq_zero]
  decide +kernel

private def detectingRow : NaturalModule :=
  fun i => if (215299268287433 : ℕ).testBit i.val then 1 else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem detectingRow_fixed : Matrix.vecMul detectingRow matrixA = detectingRow := by
  decide +kernel

private theorem detectingRow_pairing : detectingRow ⬝ᵥ distinguishedVector = 1 := by
  decide +kernel

theorem distinguishedVector_not_mem_displacementVectors :
    distinguishedVector ∉ displacementVectors := by
  rintro ⟨v, hv⟩
  have h : detectingRow ⬝ᵥ displacement v = 0 := by
    rw [displacement_apply, dotProduct_sub, Matrix.dotProduct_mulVec, detectingRow_fixed,
      sub_self]
  rw [hv, detectingRow_pairing] at h
  exact one_ne_zero h

def distinguishedFixedVector : fixedVectors := ⟨distinguishedVector, distinguishedVector_fixed⟩

/-- Its nonzero class in ker(a - 1) / im(a - 1). -/
def distinguishedClass : NaturalHomology := Submodule.Quotient.mk distinguishedFixedVector

theorem distinguishedClass_ne_zero : distinguishedClass ≠ 0 := by
  intro he
  have hm := (Submodule.Quotient.mk_eq_zero displacementInFixed).mp he
  exact distinguishedVector_not_mem_displacementVectors hm

abbrev HomologyUnit := (Module.End (ZMod 2) NaturalHomology)ˣ

instance naturalHomologyFinite : Finite NaturalHomology :=
  Finite.of_surjective (Submodule.Quotient.mk : fixedVectors → NaturalHomology)
    (Submodule.Quotient.mk_surjective displacementInFixed)

instance homologyUnitFinite : Finite HomologyUnit :=
  Finite.of_injective
    (fun u : HomologyUnit => (u : Module.End (ZMod 2) NaturalHomology).toFun)
    (by intro u v h; apply Units.ext; exact LinearMap.ext (congrFun h))

/-- The actual local word-subgroup orbit of the specified homology class. -/
def distinguishedOrbit : Set NaturalHomology :=
  {v | ∃ g : localSubgroup, (localHomologyAction g : Module.End (ZMod 2) NaturalHomology)
    distinguishedClass = v}

theorem distinguishedClass_mem_orbit : distinguishedClass ∈ distinguishedOrbit := by
  exact ⟨1, by simp⟩

theorem zero_not_mem_distinguishedOrbit : (0 : NaturalHomology) ∉ distinguishedOrbit := by
  rintro ⟨g, hg⟩
  apply distinguishedClass_ne_zero
  have he := congrArg
    (fun v => (↑(localHomologyAction g)⁻¹ : Module.End (ZMod 2) NaturalHomology) v) hg
  simpa only [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply, map_zero] using he

theorem localHomologyAction_preserves_orbit (g : localSubgroup) (v : NaturalHomology) :
    v ∈ distinguishedOrbit ↔
      (localHomologyAction g : Module.End (ZMod 2) NaturalHomology) v ∈ distinguishedOrbit := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨g * h, by simp [Module.End.mul_apply]⟩
  · rintro ⟨h, hh⟩
    refine ⟨g⁻¹ * h, ?_⟩
    rw [map_mul, map_inv]
    change (↑(localHomologyAction g)⁻¹ : Module.End (ZMod 2) NaturalHomology)
      ((localHomologyAction h : Module.End (ZMod 2) NaturalHomology) distinguishedClass) = v
    rw [hh, ← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]

/-- Linear automorphisms preserving the whole distinguished orbit setwise. -/
def orbitLinearStabilizer : Subgroup HomologyUnit where
  carrier := {u | ∀ v : NaturalHomology, v ∈ distinguishedOrbit ↔
    (u : Module.End (ZMod 2) NaturalHomology) v ∈ distinguishedOrbit}
  one_mem' := by intro v; rfl
  mul_mem' := by
    intro g h hg hh v
    exact (hh v).trans (hg ((h : Module.End (ZMod 2) NaturalHomology) v))
  inv_mem' := by
    intro g hg v
    have he := hg ((↑g⁻¹ : Module.End (ZMod 2) NaturalHomology) v)
    rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply] at he
    exact he.symm

theorem localHomologyAction_range_le_orbitLinearStabilizer :
    localHomologyAction.range ≤ orbitLinearStabilizer := by
  rintro u ⟨g, rfl⟩
  exact localHomologyAction_preserves_orbit g

theorem homologyAction_range_le_orbitLinearStabilizer
    (hpres : ∀ (c : involutionCentralizer) (v : NaturalHomology),
      v ∈ distinguishedOrbit →
        (homologyAction c : Module.End (ZMod 2) NaturalHomology) v ∈ distinguishedOrbit) :
    homologyAction.range ≤ orbitLinearStabilizer := by
  rintro u ⟨c, rfl⟩ v
  refine ⟨hpres c v, ?_⟩
  intro hv
  have hi := hpres c⁻¹ _ hv
  simpa only [map_inv, ← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply] using hi

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation
