module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Normalizers

/-!
# Coordinates on the original fixed-space preimage

Restrict the original section coordinates U → U/V₁ to the actual K-fixed
preimage U₀. The original projection identifies the fixed space with its
kernel, so this restriction maps onto Multiplicative (ker p) and has kernel
exactly the original point V₁ inside U₀. Surjectivity lifts through the
original section map; the kernel calculation retains its given V₁ kernel.

These coordinates are shared by the rechoice and order-two arguments.
They require no descent of the H-action through H/O₂(H).

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.7.63–64, printed p.1069; the U₀ calculations in 14.7.69–70,
printed pp.1072–1074.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
open Subgroup Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- U₀ maps onto the literal kernel of the original natural projection. -/
def fixedCoordinates : d.U₀ →* Multiplicative d.projection.toLinearMap.ker where
  toFun u := Multiplicative.ofAdd ⟨(d.conjugationSection.coordinates
    ⟨u, d.U₀_le_U u.property⟩).toAdd,
    (d.mem_U₀ ⟨u, d.U₀_le_U u.property⟩).mp u.property⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd d.conjugationSection.coordinates.map_one
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (d.conjugationSection.coordinates.map_mul
      ⟨a, d.U₀_le_U a.property⟩ ⟨b, d.U₀_le_U b.property⟩)

theorem fixedCoordinates_surjective : Function.Surjective d.fixedCoordinates := by
  intro w
  obtain ⟨a, ha⟩ := d.conjugationSection.onto (Multiplicative.ofAdd w.toAdd.val)
  have ha₀ : (a : G) ∈ d.U₀ := (d.mem_U₀ a).mpr (by
    rw [ha]
    exact w.toAdd.property)
  refine ⟨⟨a, ha₀⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact congrArg Multiplicative.toAdd ha

theorem fixedCoordinates_ker : d.fixedCoordinates.ker = (F.Vi 1).subgroupOf d.U₀ := by
  ext a
  change d.fixedCoordinates a = 1 ↔ (a : G) ∈ F.Vi 1
  rw [← d.conjugationSection.coordinates_eq_one_iff ⟨a, d.U₀_le_U a.property⟩]
  constructor
  · intro h
    exact congrArg (fun x : Multiplicative d.projection.toLinearMap.ker =>
      Multiplicative.ofAdd x.toAdd.val) h
  · intro h
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd h

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
