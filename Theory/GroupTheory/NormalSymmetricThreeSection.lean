module
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.GroupTheory.PResidual.NormalizerImage
public import Theory.PGroupCore

/-!
# A normal cubic detected by an action on three letters

A normal subgroup with a faithful three-letter action and even order is S₃
when the ambient two-core is trivial. Its characteristic two-residual
therefore gives a normal subgroup of order three in the original ambient group.

Source application: the doubled A₅ component in Aschbacher–Smith G.11.8
and original 14.3.15, pp.368–369,994.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem normal_cubic_of_normal_symmetric_three_embedding
    (C : Subgroup G) [C.Normal] (hcore : pCore 2 G = ⊥)
    (j : C →* Equiv.Perm (Fin 3)) (hj : Function.Injective j)
    (htwo : 2 ∣ Nat.card C) :
    ∃ Q : Subgroup G, Q.Normal ∧ Nat.card Q = 3 ∧ Q ≤ C := by
  have hcC : pCore 2 C = ⊥ := by
    apply ((pCore 2 C).map_eq_bot_iff_of_injective C.subtype_injective).mp
    apply bot_unique
    rw [← hcore]
    exact le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,pCore_isPGroup.map _⟩
  have hd : Nat.card C ∣ 6 := by
    simpa only [Nat.card_perm,Nat.card_fin,show Nat.factorial 3 = 6 from rfl] using
      Subgroup.card_dvd_of_injective j hj
  have hC6 : Nat.card C = 6 := by
    have hlist : Nat.card C = 1 ∨ Nat.card C = 2 ∨ Nat.card C = 3 ∨ Nat.card C = 6 := by
      have hh := Nat.mem_divisors.mpr ⟨hd,(by decide : 6 ≠ 0)⟩
      rw [show Nat.divisors 6 = {1,2,3,6} by decide] at hh
      simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
    rcases hlist with h | h | h | h
    · omega
    · have hP : IsPGroup 2 C := IsPGroup.of_card (n := 1) (by simpa using h)
      have ht : pCore 2 C = ⊤ := top_unique (le_sSup ⟨inferInstance,hP.to_subgroup ⊤⟩)
      have he : Nat.card C = 1 := by
        have hh := congrArg (fun Q : Subgroup C => Nat.card Q) (hcC.symm.trans ht)
        simpa only [card_bot,card_top] using hh.symm
      omega
    · omega
    · exact h
  let e : C ≃* Equiv.Perm (Fin 3) := MulEquiv.ofBijective j
    (hj.bijective_of_nat_card_le (by
      rw [hC6,Nat.card_perm,Nat.card_fin]
      decide))
  let Q := (pResidual 2 C).map C.subtype
  refine ⟨Q,ConjAct.normal_of_characteristic_of_normal,?_,map_subtype_le _⟩
  change Nat.card ((pResidual 2 C).map C.subtype) = 3
  rw [card_map_of_injective C.subtype_injective,
    ← card_map_of_injective (K := pResidual 2 C) (f := e.toMonoidHom) e.injective,
    map_pResidual,Equiv.Perm.twoResidual_eq_alternating,nat_card_alternatingGroup,Nat.card_fin]
  rfl
end Theory.GroupTheory
