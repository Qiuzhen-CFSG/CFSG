module
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Reflecting C-component normality through a solvable-kernel surjection

The quotient correspondence for C-components also reflects normality for an
arbitrary surjective homomorphism with solvable kernel. Factor the map through
its kernel quotient and use the existing normalizer correspondence there.
This is A.3.3 quotient calculus, used in the C.2.13 contained-Fitting argument.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A solvable-kernel surjection reflects normality of a C-component. -/
theorem cComponent_normal_of_solvable_image_normal {X : Type*} [Group X] {B : Subgroup G}
    (hB : B.IsCComponent) (f : G →* X) (hf : Function.Surjective f)
    [Group.IsSolvable f.ker] (hn : (B.map f).Normal) : B.Normal := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have he : (B.map (QuotientGroup.mk' f.ker)).map e.toMonoidHom = B.map f := by
    rw [map_map]
    rfl
  let := hn
  have hh : ((B.map f).comap e.toMonoidHom).Normal := inferInstance
  rw [←he] at hh
  rw [comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective] at hh
  exact cComponent_normal_of_quotient_normal hB f.ker hh

end Subgroup
