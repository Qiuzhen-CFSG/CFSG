module
public import Theory.Representation.SimpleHeadQuotient
import all Theory.Representation.SimpleHeadQuotient

/-!
# Independent inequivalent simple quotients

Two surjections onto inequivalent simple representations combine to a
surjection onto their product. Their distinct maximal invariant kernels
sum to the whole source, giving the simultaneous lifting of two vectors.
No semisimplicity of the source is required.

This extension deliberately imports the private same-kernel equivalence
construction from `SimpleHeadQuotient`; its public statement only uses
intertwining maps and representation equivalence. The binary SL₃(2)
outer-automorphism recognition consumes this product surjection.
-/

public section
namespace Representation.SimpleHeadQuotient
variable {k G M A B : Type*} [Field k] [Group G]
  [AddCommGroup M] [Module k M] [AddCommGroup A] [Module k A]
  [AddCommGroup B] [Module k B]
  {ρ : Representation k G M} {σ : Representation k G A} {τ : Representation k G B}

theorem surjective_prod_of_inequivalent_simple_quotients
    [IsIrreducible σ] [IsIrreducible τ]
    (f : ρ.IntertwiningMap σ) (g : ρ.IntertwiningMap τ)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hne : ¬ Nonempty (σ.Equiv τ)) : Function.Surjective (f.prod g) := by
  have hker : f.ker ≠ g.ker := fun he =>
    hne (equiv_of_surjective_of_ker_eq f hf g hg he)
  have hfc := isCoatom_ker_of_surjective f hf
  have hgc := isCoatom_ker_of_surjective g hg
  have hnot : ¬ g.ker ≤ f.ker := by
    intro hle
    exact hker ((hgc.le_iff_eq hfc.ne_top).mp hle)
  have hsup : f.ker ⊔ g.ker = ⊤ := hfc.2 _ (lt_of_le_of_ne le_sup_left (fun he => hnot (he ▸ le_sup_right)))
  have hs : LinearMap.ker f.toLinearMap ⊔ LinearMap.ker g.toLinearMap = ⊤ := by
    have hh := congrArg Subrepresentation.toSubmodule hsup
    rw [Subrepresentation.toSubmodule_sup] at hh
    exact hh
  rintro ⟨a,b⟩
  obtain ⟨u,hu⟩ := hf a
  obtain ⟨v,hv⟩ := hg (b - g u)
  obtain ⟨w,hw,z,hz,hwz⟩ := Submodule.mem_sup.mp
    (show v ∈ LinearMap.ker f.toLinearMap ⊔ LinearMap.ker g.toLinearMap from
      hs.symm ▸ Submodule.mem_top)
  have hgw : g w = b - g u := by
    rw [←hwz,map_add,show g z = 0 from hz,add_zero] at hv
    exact hv
  refine ⟨u+w,Prod.ext ?_ ?_⟩
  · change f (u+w) = a
    rw [map_add,show f w = 0 from hw,add_zero,hu]
  · change g (u+w) = b
    rw [map_add,hgw,add_sub_cancel]
end Representation.SimpleHeadQuotient
