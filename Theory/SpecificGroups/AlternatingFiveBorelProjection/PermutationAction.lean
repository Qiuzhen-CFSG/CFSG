module
public import Theory.SpecificGroups.AlternatingFiveBorelProjection
/-!
# Agreement of permutation and inner projections

The ambient permutation action on a natural A₅ constituent agrees exactly
with the inner projection of an actor on the component. Faithfulness of
S₅ conjugation on A₅ proves this with the original group marking.
Source application: Aschbacher–Smith, 13.6.15, printed p.930.
-/

public section
open Subgroup
namespace AlternatingFiveProjection
variable {D H : Type*} [Group D] [Group H]
theorem permutation_eq_projection (C : Subgroup D)
    (e : C ≃* alternatingGroup (Fin 5)) (r : D →* Equiv.Perm (Fin 5))
    (hr : ∀ c : C, r c.val = (e c).val)
    (q : H →* D) (f : H →* C)
    (hf : ∀ (h : H) (c : C), (f h : D)*c*(f h : D)⁻¹=q h*c*(q h)⁻¹)
    (h : H) : r (q h) = (e (f h)).val := by
  apply (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide)).injective
  apply MulEquiv.ext
  intro x
  obtain ⟨c,rfl⟩ := e.surjective x
  apply Subtype.ext
  change r (q h) * (e c).val * (r (q h))⁻¹ = (e (f h)).val * (e c).val * ((e (f h)).val)⁻¹
  have ht := congrArg r (hf h c)
  simpa only [map_mul,map_inv,hr] using ht.symm
theorem inner_projection_eq_of_range_le (C : Subgroup D)
    (e : C ≃* alternatingGroup (Fin 5))
    (q : H →* D) (f : H →* C)
    (hf : ∀ (h : H) (c : C), (f h : D)*c*(f h : D)⁻¹=q h*c*(q h)⁻¹)
    (hq : q.range ≤ C) (h : H) : (f h : D)=q h := by
  have hi : Function.Injective (MulAut.conj : C →* MulAut C) := by
    intro x y he
    apply e.injective
    apply MulAut.conj_injective_of_center_eq_bot (alternatingGroup.center_eq_bot (by simp))
    rw [← MulAut.congr_conj e x, ← MulAut.congr_conj e y, he]
  let k : C := ⟨q h,hq ⟨h,rfl⟩⟩
  have he : f h=k := by
    apply hi
    apply MulEquiv.ext
    intro c
    apply Subtype.ext
    exact hf h c
  exact congrArg Subtype.val he

end AlternatingFiveProjection
