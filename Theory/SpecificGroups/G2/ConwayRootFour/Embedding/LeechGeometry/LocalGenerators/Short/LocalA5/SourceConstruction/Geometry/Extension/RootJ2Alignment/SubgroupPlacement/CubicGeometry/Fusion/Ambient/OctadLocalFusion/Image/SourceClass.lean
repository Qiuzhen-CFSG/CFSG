module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.Geometry
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# The literal quaternion commutator class in the octad centralizer

The source's Δ_H consists of cyclic cubic subgroups whose commutator with Q is
quaternion of order eight. Here Q is the actual octad restriction kernel, and
the commutator is formed inside its original integral centralizer. The original
central quotient is injective on Q: global negation cannot fix the nonzero
rank-eight octad lattice. Consequently the quaternion condition agrees exactly
with the condition on the mapped commutator in the central quotient.

`PolynomialClassSelection` and `QuaternionImageFusion` are separate unproved
obligations. The first requires the polynomial on the whole Leech lattice;
the second requires a conjugator in the actual image. Neither follows merely
from the definitions or the two-group kernel theorem.

Source: Aschbacher, *Sporadic Groups* (1994), 25.1–25.2 (the integral Q and its
central quotient), §46, p.251 (the definition of Δ_H), and 49.3(2), pp.280–281.
Exercise 9.6, p.141, proves only the forward fixed-free property of the specified
class and does not supply `PolynomialClassSelection`.
-/

@[expose] public noncomputable section

open Atlas.Codes Atlas.Lattices Atlas.Conway
open scoped BigOperators
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction

def kernelCommutator (r : centralizer) : Subgroup centralizer :=
  ⁅action.ker, Subgroup.zpowers r⁆

theorem kernelCommutator_le (r : centralizer) : kernelCommutator r ≤ action.ker :=
  Subgroup.commutator_le_left _ _

def QuaternionCubic (r : centralizer) : Prop :=
  Nonempty (kernelCommutator r ≃* QuaternionGroup 2)

theorem kernelCommutator_map_projection (r : centralizer) :
    (kernelCommutator r).map projection =
      ⁅action.ker.map projection, Subgroup.zpowers (projection r)⁆ := by
  rw [kernelCommutator, Subgroup.map_commutator, MonoidHom.map_zpowers]

theorem kernel_projection_injective :
    Function.Injective (projection.comp action.ker.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm _ bot_le
  intro g hg
  change g = 1
  have hp : projection g.val = 1 := hg
  have hc : g.val.val ∈ leechCentralSigns := by
    rw [← leechCentralProjection_kernel]
    exact hp
  rcases (leechCentralSigns_mem g.val.val).mp hc with hc | hc
  · apply Subtype.ext
    exact Subtype.ext hc
  · have hne : Nonempty Coordinate := Fintype.card_pos_iff.mp (by rw [coordinate_card]; decide)
    obtain ⟨i⟩ := hne
    have hfix := (mem_action_ker g.val).mp g.prop (scaledCoordinates (fun _ => 1))
    rw [hc, negationIsometry_apply] at hfix
    have he := congrArg (fun x : leech => x.val i.val) hfix
    simp [scaledCoordinates, eightIntoLeech, extendCoordinates, i.prop] at he

def kernelCommutatorProjectionEquiv (r : centralizer) :
    kernelCommutator r ≃* (kernelCommutator r).map projection :=
  MulEquiv.ofBijective (projection.subgroupMap (kernelCommutator r)) ⟨by
    intro x y h
    have he : projection x.val = projection y.val := congrArg Subtype.val h
    have hk := kernel_projection_injective (a₁ := ⟨x.val, kernelCommutator_le r x.prop⟩)
      (a₂ := ⟨y.val, kernelCommutator_le r y.prop⟩) he
    exact Subtype.ext (congrArg (fun q : action.ker => q.val) hk),
    projection.subgroupMap_surjective _⟩

theorem quaternionCubic_iff_centralQuotient (r : centralizer) :
    QuaternionCubic r ↔
      Nonempty ((⁅action.ker.map projection, Subgroup.zpowers (projection r)⁆ :
        Subgroup LeechCentralQuotient) ≃* QuaternionGroup 2) := by
  rw [← kernelCommutator_map_projection]
  constructor
  · rintro ⟨e⟩
    exact ⟨(kernelCommutatorProjectionEquiv r).symm.trans e⟩
  · rintro ⟨e⟩
    exact ⟨(kernelCommutatorProjectionEquiv r).trans e⟩

def PolynomialClassSelection : Prop :=
  ∀ r : centralizer, orderOf r = 3 →
    (∀ x : leech, r.val.val (r.val.val x) + r.val.val x + x = 0) → QuaternionCubic r

def QuaternionImageFusion : Prop :=
  ∀ r s : centralizer, orderOf r = 3 → orderOf s = 3 → QuaternionCubic r → QuaternionCubic s →
    ∃ c : Image, Subgroup.zpowers (action r) =
      (Subgroup.zpowers (action s)).map (MulAut.conj c.val).toMonoidHom


end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
