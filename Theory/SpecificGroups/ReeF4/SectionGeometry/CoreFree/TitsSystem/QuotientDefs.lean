module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.Basic
public import Theory.AlgebraicGroup.BNPair.Defs

/-!
# The marked quotient for the concrete Ree normalizer

The simple classes are the images of the actual two fixed orbit words. This
interface assumes only the normality needed to form the quotient group; its
construction, quotient generation, and the exchange calculation have separate
owners. In particular, no BN-pair or group simplicity is included as data.

Source: GLS3 2.3.4(a,b), `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section
noncomputable section
namespace ReeF4.SectionGeometry.BNPair
open Subgroup LargeLocalSeeds Parabolics

/-- The Weyl quotient, once normality of the specified intersection is proved. -/
abbrev WeylQuotient (m : ℕ) :=
  normalizerWords m ⧸ (borel m ⊓ normalizerWords m).subgroupOf (normalizerWords m)

variable (m : ℕ)
variable [((borel m ⊓ normalizerWords m).subgroupOf (normalizerWords m)).Normal]

/-- The class of the longest word on a specified exceptional node orbit. -/
def simpleReflection (s : Side) : WeylQuotient m :=
  QuotientGroup.mk' _ (simpleLift m s)

/-- The marked pair of relative simple reflections. -/
def simpleReflections : Set (WeylQuotient m) := Set.range (simpleReflection m)

@[simp] theorem simpleReflection_mem (s : Side) :
    simpleReflection m s ∈ simpleReflections m := Set.mem_range_self s

theorem simpleReflections_eq_pair :
    simpleReflections m = {simpleReflection m .linear, simpleReflection m .suzuki} := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    cases s <;> simp
  · intro hx
    rcases hx with rfl | hx
    · exact Set.mem_range_self _
    · rw [Set.mem_singleton_iff] at hx
      subst x
      exact Set.mem_range_self _

theorem simpleReflections_finite : (simpleReflections m).Finite := by
  exact Set.toFinite _

/-- Both simple classes square to one, before proving they are nonidentity. -/
theorem simpleReflection_sq (s : Side) : simpleReflection m s ^ 2 = 1 := by
  rw [simpleReflection, ← map_pow, simpleLift_sq, map_one]

/-- Removing the middle-node reflection retains precisely the end-node one. -/
theorem simpleReflections_sdiff_suzuki
    (h : simpleReflection m .linear ≠ simpleReflection m .suzuki) :
    simpleReflections m \ {simpleReflection m .suzuki} = {simpleReflection m .linear} := by
  rw [simpleReflections_eq_pair]
  ext x
  simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
  aesop

end ReeF4.SectionGeometry.BNPair
