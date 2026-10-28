module
public import Theory.Representation.BinaryConjugationSection

/-!
# Keeping a conjugation section inside its local ambient group

Restrict ambient membership through the actual subgroup inclusion, while
transporting actor and section elements through the canonical subgroup
identifications. Coordinates, their exact kernel, and conjugation remain
unchanged. This supports passage from an ambient source module to a block
inside its original local group (Aschbacher–Smith 10.2.3(4), p.746).
-/

public noncomputable section
namespace Representation.BinaryConjugationSection
open Subgroup
variable {G : Type*} [Group G] {H A B : Subgroup G}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) H V} (c : BinaryConjugationSection H A B ρ)

/-- Express the same section inside a specified local ambient group. -/
def subgroupOf (N : Subgroup G) (hHN : H ≤ N) :
    BinaryConjugationSection (H.subgroupOf N) (A.subgroupOf N) (B.subgroupOf N)
      (ρ.comp (subgroupOfEquivOfLe hHN).toMonoidHom) where
  section_le := fun _ hx => c.section_le hx
  kernel_le := fun _ hx => c.kernel_le hx
  normalized := by
    intro h hh
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (c.normalized hh) (a:G)
  coordinates := c.coordinates.comp (subgroupOfEquivOfLe (c.section_le.trans hHN)).toMonoidHom
  onto := c.onto.comp (subgroupOfEquivOfLe (c.section_le.trans hHN)).surjective
  kernel_eq := by
    ext a
    exact c.coordinates_eq_one_iff ((subgroupOfEquivOfLe (c.section_le.trans hHN)) a)
  equivariant h a := c.equivariant ((subgroupOfEquivOfLe hHN) h)
    ((subgroupOfEquivOfLe (c.section_le.trans hHN)) a)
end Representation.BinaryConjugationSection
