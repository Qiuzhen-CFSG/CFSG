module

public import Theory.GroupTheory.CComponent.OrbitCorrespondence
public import Theory.GroupTheory.SubgroupConjugation

/-!
# A fixed component in a generated component orbit

If a C-component and a p-subgroup generate the group, every C-component
belongs to that p-subgroup's conjugacy orbit. A component fixed by the
p-subgroup is therefore the original generating component.

Source: the component-orbit argument of Aschbacher--Smith A.3.8(3), p.45.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A component normalized by the generating p-subgroup equals the generating component. -/
theorem IsCComponent.eq_of_pGroup_generated_of_normalized
    {X B S : Subgroup G} (hX : X.IsCComponent) (hB : B.IsCComponent)
    (hS : IsPGroup p S) (hgen : X ⊔ S = ⊤)
    (hSB : S ≤ normalizer (B : Set G)) : B = X := by
  obtain ⟨s, hs⟩ := hX.conjugate_of_pGroup_generated hB hS hgen
  have hi := congrArg (fun A : Subgroup G => A.conjBy (s : G)⁻¹) hs
  change B.conjBy (s : G)⁻¹ = (X.conjBy (s : G)).conjBy (s : G)⁻¹ at hi
  rw [conjBy_inv] at hi
  have hb : B.conjBy (s : G)⁻¹ = B :=
    mem_normalizer_iff_map_conj_eq.mp (hSB (S.inv_mem s.property))
  exact hb.symm.trans hi

end Subgroup
