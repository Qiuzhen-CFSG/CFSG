module

public import Theory.GroupTheory.SolvableResidual.Transport

/-!
# The perfect factor of a solvable-by-perfect product quotient

A surjection onto A × B restricts on the solvable residual to a surjection
onto the perfect factor B. If A is solvable, that restriction kills A;
thus a prime-group kernel remains a prime-group kernel after projection.
The maps retain the original homomorphism on representatives.

Source application: the 2+3 and 3+2 flag residuals in Aschbacher--Smith,
Notation 12.8.2 and Lemma 12.9.3, printed pp.849 and858.
-/

@[expose] public section
open Subgroup
namespace MonoidHom
variable {X A B : Type*} [Group X] [Group A] [Group B]

/-- Restrict the perfect factor of a product quotient to the solvable residual. -/
def solvableResidualPerfectFactor (f : X →* A × B) : solvableResidual X →* B :=
  ((MonoidHom.snd A B).comp f).comp (solvableResidual X).subtype

theorem solvableResidualPerfectFactor_surjective [Finite X] [Group.IsPerfect B]
    (f : X →* A × B) (hf : Function.Surjective f) :
    Function.Surjective f.solvableResidualPerfectFactor := by
  let g := (MonoidHom.snd A B).comp f
  have hg : Function.Surjective g := (show Function.Surjective (MonoidHom.snd A B) from fun b => ⟨(1,b),rfl⟩).comp hf
  have hm : (solvableResidual X).map g = ⊤ := by
    rw [map_solvableResidual_eq g hg, solvableResidual_eq_top]
  intro b
  obtain ⟨x,hx,he⟩ := mem_map.mp (hm.symm ▸ (mem_top b))
  exact ⟨⟨x,hx⟩,he⟩

theorem solvableResidualPerfectFactor_ker_isPGroup [Group.IsSolvable A]
    {p : ℕ} (f : X →* A × B) (hk : IsPGroup p f.ker) :
    IsPGroup p f.solvableResidualPerfectFactor.ker := by
  apply (hk.comap_of_injective (solvableResidual X).subtype Subtype.val_injective).to_le
  intro x hx
  change f x.val = 1
  apply Prod.ext
  · have hm := map_solvableResidual_le ((MonoidHom.fst A B).comp f)
      (mem_map_of_mem _ x.property)
    rw [solvableResidual_eq_bot] at hm
    exact mem_bot.mp hm
  · exact hx
end MonoidHom
