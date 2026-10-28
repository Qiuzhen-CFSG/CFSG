module

/-
Adapted from Atlas/Comparisons/Exceptional/SingerEightAction.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917, by Gerald Höhn
and the ATLAS contributors. ATLAS Research and Attribution License 1.0
applies; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Changes: Lean 4.33 module boundaries, narrow imports, and CFSG order APIs.
-/

public import Theory.AtlasPort.ExceptionalIsomorphisms.SingerEight
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models
public import Theory.AtlasPort.ExceptionalIsomorphisms.SimpleOrder168Sylow
set_option warningAsError false

@[expose] public section

/-!
# Conjugation on the eight Singer subgroups

The eight explicitly marked cyclic subgroups are all the Sylow seven-subgroups
of SL₃(2). Simplicity makes the conjugation action faithful. The previously
checked matrix identities identify two permutations with translation and
inversion on the marked projective line over the seven-element field.
-/


namespace Atlas.Comparisons.Exceptional.SingerEight
open MulAction
local instance singerEightActionPrime1 : Fact (Nat.Prime 7) := ⟨by decide⟩

noncomputable def sylow (i : Fin 8) : Sylow 7 G :=
  Sylow.ofCard (subgroup i) (by
    rw [subgroup_card, sl3Two_card]
    rw [show 168 = 7 * 24 from rfl,
      Nat.factorization_mul_apply_of_coprime (by decide : Nat.Coprime 7 24),
      (by decide : Nat.Prime 7).factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 24)]
    norm_num)

theorem sylow_subgroup (i : Fin 8) : (sylow i).toSubgroup = subgroup i := rfl

theorem sylow_bijective : Function.Bijective sylow := by
  apply (Nat.bijective_iff_injective_and_card sylow).mpr
  refine ⟨?_, ?_⟩
  · intro i j h
    exact subgroup_injective (congrArg Sylow.toSubgroup h)
  · let := sl3Two_simple
    rw [Nat.card_fin, Atlas.GroupTheory.simple_order_168_sylow_seven_count sl3Two_card]

noncomputable def sylowEquiv : Fin 8 ≃ Sylow 7 G := Equiv.ofBijective sylow sylow_bijective

noncomputable def action : G →* Equiv.Perm (Fin 8) :=
  (Equiv.permCongrHom sylowEquiv.symm).toMonoidHom.comp (MulAction.toPermHom G (Sylow 7 G))

theorem action_injective : Function.Injective action := by
  let := sl3Two_simple
  exact (Equiv.permCongrHom sylowEquiv.symm).injective.comp
    (Atlas.GroupTheory.simple_order_168_sylow_seven_action_injective sl3Two_card)

theorem sylow_U (i : Fin 8) : U • sylow i = sylow (shift i) := by
  apply Sylow.ext
  exact subgroup_U i

theorem sylow_T (i : Fin 8) : T • sylow i = sylow (invert i) := by
  apply Sylow.ext
  exact subgroup_T i

theorem action_U (i : Fin 8) : action U i = shift i := by
  change sylowEquiv.symm (U • sylow i) = shift i
  rw [sylow_U]
  exact sylowEquiv.symm_apply_apply _

theorem action_T (i : Fin 8) : action T i = invert i := by
  change sylowEquiv.symm (T • sylow i) = invert i
  rw [sylow_T]
  exact sylowEquiv.symm_apply_apply _

end Atlas.Comparisons.Exceptional.SingerEight
