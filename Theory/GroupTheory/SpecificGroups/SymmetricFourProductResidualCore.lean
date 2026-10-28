module
public import Theory.GroupTheory.PResidual.PGroupFactor
public import Theory.SpecificGroups.SymmetricFourResidualCore
public import Theory.GroupTheory.PCoreActionSplitting

/-!
# The literal four-group in the residual of C₂ × S₄

Projection to S₄ identifies the two-residual with the alternating subgroup.
The Klein four two-core of S₄ is absorbed by its two-residual, so its literal
inverse image under the second-factor inclusion is the required residual
core. The equality retains that inclusion, allowing independent endpoint
representations to compare the two four-groups in a common source subgroup.

Source application: Aschbacher–Smith F.5.5, printed pp.301–302.
-/

@[expose] public noncomputable section
namespace Theory.GroupTheory.SymmetricFourResidualCore
open Subgroup
open Theory.SpecificGroups.SymmetricSix.DuadCalculation
local notation "C2" => Multiplicative (ZMod 2)
local notation "S4" => Equiv.Perm (Fin 4)

private theorem c2_two : IsPGroup 2 C2 :=
  IsPGroup.of_card (n := 1) (by norm_num [Nat.card_eq_fintype_card])

/-- The core of O²(C₂×S₄) is the literal Klein four in the second factor. -/
theorem residual_core_image {X : Type*} [Group X] [Finite X]
    (e : X ≃* C2 × S4) :
    (pCore 2 (pResidual 2 X)).map (pResidual 2 X).subtype =
      core.map (e.symm.toMonoidHom.comp (MonoidHom.inr C2 S4)) := by
  let r := pResidualEquivOfPGroupFactor 2 e c2_two
  have hr : (pCore 2 (pResidual 2 X)).map r.toMonoidHom =
      pCore 2 (pResidual 2 S4) := pCore_map_iso 2 r
  have hcore : (pCore 2 (pResidual 2 S4)).map (pResidual 2 S4).subtype = core := by
    rw [core_eq]
    exact (pCore_eq_map_of_normal_of_le 2 (pResidual 2 S4)
      Theory.SpecificGroups.SymmetricFour.twoCore_le_twoResidual).symm
  have heq : (pResidual 2 X).subtype =
      (e.symm.toMonoidHom.comp (MonoidHom.inr C2 S4)).comp
        ((pResidual 2 S4).subtype.comp r.toMonoidHom) := by
    apply MonoidHom.ext
    intro x
    apply e.injective
    change e x.val = e (e.symm (1, (r x).val))
    rw [e.apply_symm_apply]
    exact Prod.ext (fst_eq_one_of_mem_pResidual 2 e c2_two x.property)
      (pResidualEquivOfPGroupFactor_apply 2 e c2_two x).symm
  rw [heq]
  simp only [←map_map]
  rw [hr,hcore]

/-- In particular the embedded residual core is elementary of order four. -/
theorem residual_core_card {X : Type*} [Group X] [Finite X]
    (e : X ≃* C2 × S4) : Nat.card (pCore 2 (pResidual 2 X)) = 4 := by
  have he := congrArg (fun K : Subgroup X => Nat.card K) (residual_core_image e)
  rw [card_map_of_injective (pResidual 2 X).subtype_injective,
    card_map_of_injective (e.symm.injective.comp (by
      intro a b h; exact congrArg Prod.snd h)),core_card] at he
  exact he

end Theory.GroupTheory.SymmetricFourResidualCore
