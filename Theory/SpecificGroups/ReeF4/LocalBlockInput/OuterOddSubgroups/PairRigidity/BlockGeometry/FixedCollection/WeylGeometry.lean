module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.PositiveFactors
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.WeylWords
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.WeylGeometry.LinearWord
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.WeylGeometry.SuzukiWord

/-!
# Signed fixed-block Weyl words and the eight positive block orbits

The two specified relative Weyl representatives are words in their signed
fixed blocks: three factors for the linear side, and five central factors
for the Suzuki side. Explicit products of those representatives carry the
simple pair and the complete simple B₂ quartet to all eight positive blocks.
The exported `positiveBlock_weyl_orbit` transports every root parameter,
including both nonsimple roots of every B₂ quartet.

These are exactly the two geometric inputs to fixed positive collection.
They hold for every supplied local twist and every parameter `m`.

Source: GLS3, 2.3.2–8 and Table 2.4,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection
open LargeLocalSeeds
variable {m : ℕ}

/-- Both specified relative Weyl words belong to their signed fixed blocks. -/
theorem relativeWeyl_mem_simpleBlock_sup (d : LocalBlockInput m) (s : Side) :
    relativeWeyl d s ∈ simpleBlock d s true ⊔ simpleBlock d s false := by
  cases s with
  | linear => exact relativeWeyl_linear_mem d
  | suzuki => exact relativeWeyl_suzuki_mem d

end ReeF4.LocalBlockInput.PairRigidity.FixedCollection
