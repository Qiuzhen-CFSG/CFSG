module

public import Theory.GroupTheory.CComponent.RadicalKernel
public import Theory.GroupTheory.SolvableRadical.Transport

/-!
# Simple images of intrinsic C-components

A surjection from a finite intrinsic C-component to a simple group has
kernel equal to the solvable radical. The kernel is proper, hence solvable
by C-component minimality. Conversely, its radical has solvable normal
image in the nonabelian simple target, so that image is trivial.

Source: Aschbacher--Smith A.3.3(1), printed p.42. The intrinsic formulation
keeps this argument independent of subnormality in a larger ambient image.
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- Every simple surjective image of an intrinsic C-component has its
solvable radical as the actual homomorphism kernel. -/
theorem kernel_eq_solvableRadical_of_top_isCComponent {D S : Type*} [Group D] [Finite D] [Group S]
    [IsSimpleGroup S] (hD : (⊤ : Subgroup D).IsCComponent)
    (f : D →* S) (hf : Function.Surjective f) : f.ker = solvableRadical D := by
  let : Finite S := Finite.of_surjective f hf
  let : Group.IsPerfect (⊤ : Subgroup D) := hD.perfect
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective
    (f := (topEquiv : (⊤ : Subgroup D) ≃* D).toMonoidHom) topEquiv.surjective
  let : Group.IsPerfect S := Group.IsPerfect.ofSurjective hf
  have hs : solvableRadical S = ⊥ := by
    rcases (inferInstance : (solvableRadical S).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · have hsol : Group.IsSolvable S := Group.isSolvable_of_surjective
        (f := (solvableRadical S).subtype)
        (by intro s; exact ⟨⟨s, ht.symm ▸ mem_top s⟩, rfl⟩)
      exact (Group.IsPerfect.not_isSolvable S hsol).elim
  have hproper : f.ker ≠ ⊤ := by
    intro ht
    obtain ⟨s, hs⟩ := exists_ne (1 : S)
    obtain ⟨d, rfl⟩ := hf s
    exact hs (show f d = 1 from (ht ▸ mem_top d : d ∈ f.ker))
  apply le_antisymm (kernel_le_solvableRadical_of_top_isCComponent hD f hproper)
  have h := map_solvableRadical_le_of_surjective f hf
  rw [hs] at h
  exact map_le_iff_le_comap.mp h

end Theory.GroupTheory
