module
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.GroupTheory.PCoreSurjective
/-!
# Recognizing a defining-characteristic Sylow subgroup by its order

A two-subgroup of an SL₂ extension with two-group kernel is Sylow when
its order is the product of the kernel order and the coefficient-field order.
A containing Sylow maps onto a Sylow of SL₂; the restriction's exact kernel
and the upper-root Sylow cardinality give equality of the two subgroups.
The literal source consumer is Aschbacher–Smith, 2.4.12(2), fixed R in L.
-/
public section
open Subgroup
namespace Matrix.SpecialLinearGroup
variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F] [CharP F 2]
theorem exists_sylow_of_kernel_field_card
    (f : X →* SpecialLinearGroup (Fin 2) F) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (H : Subgroup X) (hH : IsPGroup 2 H)
    (hc : Nat.card H = Nat.card F * Nat.card f.ker) :
    ∃ P : Sylow 2 X, (P : Subgroup X) = H := by
  obtain ⟨P, hHP⟩ := hH.exists_le_sylow
  have hkP : f.ker ≤ (P : Subgroup X) := hk.le_sylow_of_normal P
  let P' := P.mapSurjective (f := f) hf
  let r := f.comp (P : Subgroup X).subtype
  have hr : r.range = (P' : Subgroup (SpecialLinearGroup (Fin 2) F)) := by
    rw [MonoidHom.range_comp, range_subtype]
    rfl
  have hker : r.ker = f.ker.subgroupOf (P : Subgroup X) := rfl
  have hkc : Nat.card r.ker = Nat.card f.ker := by
    rw [hker]
    exact Nat.card_congr (subgroupOfEquivOfLe hkP).toEquiv
  have hrc : Nat.card r.range = Nat.card F := by
    rw [hr]
    exact Nat.card_congr (sylowEquivAdditive F 2 P').symm.toEquiv
  have hPc : Nat.card P = Nat.card F * Nat.card f.ker := by
    calc
      Nat.card P = Nat.card r.ker * Nat.card r.range := by
        rw [← index_ker, r.ker.card_mul_index]
      _ = Nat.card F * Nat.card f.ker := by rw [hkc, hrc, Nat.mul_comm]
  exact ⟨P, (eq_of_le_of_card_ge hHP (by rw [hc, hPc])).symm⟩
end Matrix.SpecialLinearGroup
