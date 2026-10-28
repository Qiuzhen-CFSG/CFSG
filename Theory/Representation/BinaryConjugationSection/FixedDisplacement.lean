module
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryConjugationSection.FixedIndex
public import Theory.Representation.BinaryConjugationSection.DisplacementPreimage

/-!
# Pulling fixed-space displacement back to actual subgroups

A linear containment of component-fixed vectors in an actor's displacement
space pulls back under literal binary conjugation coordinates to a containment
of the fixed preimage in the group commutator times the coordinate kernel.
This is the fixed-kernel step in MS93 (3.6), printed p.871.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {H U Z : Subgroup G}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) H V} (d : BinaryConjugationSection H U Z ρ)
include d

theorem fixedPreimage_le_commutator_sup_of_fixed_le_moved
    (L B : Subgroup G) (hL : L ≤ H) (hB : B ≤ H)
    (hn : U ≤ normalizer (Z : Set G))
    (hfix : fixedSpace ρ (L.subgroupOf H) ≤ subspaceCommutator ρ ⊤ (B.subgroupOf H)) :
    commutatorPreimage U L Z ≤ ⁅U,B⁆ ⊔ Z := by
  have hU : d.imageSpace U = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨u,hu⟩ := d.onto (Multiplicative.ofAdd v)
    exact (d.mem_imageSpace_iff U v).mpr ⟨u,u.property,congrArg Multiplicative.toAdd hu⟩
  have hc : ⁅B,U⁆ ≤ U := le_normalizer_iff_commutator_le_right.mp (hB.trans d.normalized)
  intro x hx
  let xU : U := ⟨x,commutatorPreimage_le U L Z hx⟩
  have hm : (d.coordinates xU).toAdd ∈ d.imageSpace (commutatorPreimage U L Z) :=
    (d.mem_imageSpace_iff _ _).mpr ⟨xU,hx,rfl⟩
  rw [d.fixed_image_eq L hL hn] at hm
  have hv := hfix hm
  rw [←hU,←d.imageSpace_commutator B U hB le_rfl] at hv
  have hmem := (d.coordinates_mem_imageSpace_iff ⁅B,U⁆ hc xU).mp hv
  simpa only [commutator_comm] using hmem
end Representation.BinaryConjugationSection

