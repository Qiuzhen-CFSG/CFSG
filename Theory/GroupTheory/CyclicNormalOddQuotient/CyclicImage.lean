module

public import Theory.GroupTheory.CyclicNormalOddQuotient

/-!
# Cyclic images from a kernel comparison

If the kernel of a map to a cyclic group is killed by a second homomorphism,
the second image is cyclic. The first isomorphism theorem identifies the
intermediate quotient with a subgroup of the cyclic parameter group.
This supplies both the determinant and field-parameter steps for the
outer-automorphism calculation of GLS3, Theorem 2.5.12.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {A C G : Type*} [Group A] [Group C] [Group G]

/-- A surjective image factors through a cyclic image when its kernel contains
the parameter kernel. No choice of a splitting is required. -/
theorem isCyclic_of_surjective_of_ker_le_cyclic [IsCyclic C] (d : A →* C) (f : A →* G)
    (hf : Function.Surjective f) (hker : d.ker ≤ f.ker) : IsCyclic G := by
  let : IsCyclic (A ⧸ d.ker) :=
    isCyclic_of_injective (QuotientGroup.kerLift d) (QuotientGroup.kerLift_injective d)
  exact isCyclic_of_surjective (QuotientGroup.lift d.ker f hker)
    (QuotientGroup.lift_surjective_of_surjective d.ker f hf hker)

/-- The image of a homomorphism is cyclic if it factors through a cyclic image. -/
theorem isCyclic_range_of_ker_le_cyclic [IsCyclic C] (d : A →* C) (f : A →* G)
    (hker : d.ker ≤ f.ker) : IsCyclic f.range := by
  apply isCyclic_of_surjective_of_ker_le_cyclic d f.rangeRestrict f.rangeRestrict_surjective
  simpa only [MonoidHom.ker_rangeRestrict] using hker

end Theory.GroupTheory

