module

public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.GroupTheory.SymmetricThreeTwoCore

/-!
# Full automorphism actions on a Klein four-group

The automorphism group is isomorphic to S₃ by its action on the three
nonidentity elements. The existing order-six calculation proves this
faithful permutation action is onto. Since S₃ has trivial two-core, a
surjective action on a Klein four-group annihilates the acting group's
two-core. No two-group hypothesis on the entire action kernel is needed.

This source-neutral calculation is used in Aschbacher–Smith 15.3.66(5),
combined manuscript (1 March 2004), printed p.1152.
-/

@[expose] public section

open Subgroup
open scoped IsKleinFour
namespace IsKleinFour
variable {G : Type*} [Group G]

/-- The actual permutation action on the three nonidentity elements of a four-group. -/
noncomputable def autEquivPermThree (E : Type*) [Group E] [IsKleinFour E] :
    MulAut E ≃* Equiv.Perm (Fin 3) := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  let ρ : MulAut E →* Equiv.Perm {x : E // x ≠ 1} := {
    toFun f := Equiv.Perm.subtypePerm f.toEquiv (fun x => by simp)
    map_one' := by ext x; rfl
    map_mul' f g := by ext x; rfl }
  have hinj : Function.Injective ρ := by
    intro f g h
    ext x
    by_cases hx : x = 1
    · simp [hx]
    · exact congrArg Subtype.val (Equiv.congr_fun h ⟨x, hx⟩)
  have hc : Nat.card {x : E // x ≠ 1} = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp
  have hcard : Nat.card (MulAut E) = Nat.card (Equiv.Perm {x : E // x ≠ 1}) := by
    rw [IsKleinFour.card_mulAut, Nat.card_eq_fintype_card, Fintype.card_perm,
      ← Nat.card_eq_fintype_card, hc]
    decide
  exact (MulEquiv.ofBijective ρ ((Nat.bijective_iff_injective_and_card ρ).mpr
    ⟨hinj, hcard⟩)).trans (Equiv.permCongrHom ((Finite.equivFin _).trans (finCongr hc)))

private theorem permThree_twoCore : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
  have h := ker_eq_twoCore_of_surjective_perm_three (MonoidHom.id (Equiv.Perm (Fin 3)))
    Function.surjective_id (IsPGroup.ker_isPGroup_of_injective Function.injective_id)
  exact h.symm.trans MonoidHom.ker_id

/-- A full action on a four-group kills the acting group's normal two-core. -/
theorem twoCore_le_ker_of_surjective [Finite G]
    (E : Type*) [Group E] [IsKleinFour E] (f : G →* MulAut E)
    (hf : Function.Surjective f) : pCore 2 G ≤ f.ker := by
  let e := autEquivPermThree E
  let φ := e.toMonoidHom.comp f
  have hφ : Function.Surjective φ := e.surjective.comp hf
  have hn : ((pCore 2 G).map φ).Normal := (inferInstance : (pCore 2 G).Normal).map φ hφ
  have hp : IsPGroup 2 ((pCore 2 G).map φ) := pCore_isPGroup.map φ
  have hle : (pCore 2 G).map φ ≤ pCore 2 (Equiv.Perm (Fin 3)) := le_sSup ⟨hn, hp⟩
  rw [permThree_twoCore] at hle
  have hk := (map_eq_bot_iff (pCore 2 G)).mp (le_bot_iff.mp hle)
  simpa only [φ, MonoidHom.ker_comp_of_injective f e.toMonoidHom e.injective] using hk

end IsKleinFour
