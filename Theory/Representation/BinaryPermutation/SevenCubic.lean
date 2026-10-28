module
public import Theory.Representation.BinaryPermutation
public import Theory.Representation.BinaryGroupAction
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupAction.CoprimeMovingQuotient

/-!
# The cubic moving plane in the seven-point binary module

For the literal cycle (5,6,7), the augmentation core has order 64 and its
fixed subgroup has order 16. Four explicit coordinates parametrize that
fixed subgroup. Coprime splitting therefore gives a moving four-group.
The calculation transports to the exact natural quotient used in block
models and to equivariant projections with a central fixed kernel.

Source: the construction of Y≃A₄ in C.1.29, printed p.134.
-/
public section
open Subgroup
namespace BinaryPermutation.SevenCubic
abbrev Space := core (Fin 7)
abbrev V := Multiplicative Space
@[expose] def cycle : Equiv.Perm (Fin 7) := Equiv.swap 4 5 * Equiv.swap 5 6
abbrev C := Subgroup.zpowers cycle
noncomputable instance : MulDistribMulAction (Equiv.Perm (Fin 7)) V :=
  Representation.BinaryGroupAction.action (coreRepresentation (Fin 7))

theorem cycle_order : orderOf cycle = 3 := by
  apply orderOf_eq_prime_iff.mpr
  exact ⟨by decide, by decide⟩

theorem card_actor : Nat.card C = 3 := by rw [Nat.card_zpowers, cycle_order]

theorem card_space : Nat.card V = 64 := by
  change Nat.card Space = 64
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, finrank_core]
  decide

private theorem fixed_iff (v : Space) :
    coreRepresentation (Fin 7) cycle v = v ↔ v.val 4 = v.val 5 ∧ v.val 5 = v.val 6 := by
  constructor
  · intro he
    have h5 := congrArg (fun w : Space => w.val 5) he
    have h6 := congrArg (fun w : Space => w.val 6) he
    exact ⟨by simpa [coreRepresentation_apply, representation_apply, cycle, Equiv.swap_apply_def] using h5,
      by simpa [coreRepresentation_apply, representation_apply, cycle, Equiv.swap_apply_def] using h6⟩
  · rintro ⟨h45, h56⟩
    apply Subtype.ext
    funext i
    fin_cases i <;> norm_num [coreRepresentation_apply, representation_apply, cycle, Equiv.swap_apply_def, Fin.ext_iff, h45, h56]
    all_goals first | exact h56.symm | exact (h45.trans h56).symm | rfl

private def vector (w : Fin 4 → ZMod 2) : Space :=
  ⟨![w 0, w 1, w 2, w 0 + w 1 + w 2 + w 3, w 3, w 3, w 3], by
    rw [mem_core]
    simp [Fin.sum_univ_succ]
    ring_nf
    simp [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide]⟩

private theorem vector_fixed (w : Fin 4 → ZMod 2) :
    coreRepresentation (Fin 7) cycle (vector w) = vector w :=
  (fixed_iff _).mpr ⟨rfl, rfl⟩

private def fixedCoordinates : FixedPoints.subgroup C V ≃ (Fin 4 → ZMod 2) where
  toFun v := ![v.val.toAdd.val 0, v.val.toAdd.val 1, v.val.toAdd.val 2, v.val.toAdd.val 4]
  invFun w := ⟨Multiplicative.ofAdd (vector w), by
    intro c
    exact smul_eq_self_of_mem_zpowers c.property (vector_fixed w)⟩
  left_inv v := by
    apply Subtype.ext
    change vector ![v.val.toAdd.val 0, v.val.toAdd.val 1, v.val.toAdd.val 2, v.val.toAdd.val 4] = v.val.toAdd
    apply Subtype.ext
    have hc := v.property ⟨cycle, mem_zpowers cycle⟩
    change coreRepresentation (Fin 7) cycle v.val.toAdd = v.val.toAdd at hc
    obtain ⟨h45, h56⟩ := (fixed_iff _).mp hc
    have hsum := v.val.toAdd.property
    rw [mem_core] at hsum
    have h3 : v.val.toAdd.val 3 = v.val.toAdd.val 0 + v.val.toAdd.val 1 +
        v.val.toAdd.val 2 + v.val.toAdd.val 4 := by
      simp [Fin.sum_univ_succ, ← h45, ← h56] at hsum
      linear_combination (norm := ring_nf) hsum
      simp [show (2 : ZMod 2) = 0 by decide, show (4 : ZMod 2) = 0 by decide]
    funext i
    fin_cases i <;> simp [vector, ← h45, ← h56, h3]
  right_inv w := by funext i; fin_cases i <;> rfl

theorem card_fixed : Nat.card (FixedPoints.subgroup C V) = 16 := by
  rw [Nat.card_congr fixedCoordinates, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

theorem card_moving : Nat.card (commutatorAction C V) = 4 := by
  let F := FixedPoints.subgroup C V
  let M := commutatorAction C V
  have hcop : Nat.Coprime (Nat.card C) (Nat.card V) := by rw [card_actor, card_space]; decide
  have hc := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := V) (A := C) (Group.isSolvable_of_comm fun x y => mul_comm x y) hcop inferInstance
  have he := card_sup_eq_mul_of_normalizes_of_disjoint F M le_normalizer_of_normal hc.disjoint
  rw [hc.sup_eq_top, card_top, card_fixed, card_space] at he
  change 64 = 16 * Nat.card (commutatorAction C V) at he
  omega

/-- The four-element moving plane survives the actual fixed-kernel module
projection and any surjective marking of the cubic actor. -/
theorem card_moving_of_equivariant_projection
    {A U : Type*} [Group A] [Finite A] [Group U] [Finite U]
    [IsMulCommutative U] [MulDistribMulAction A U]
    (a : A →* C) (ha : Function.Surjective a)
    (f : U →* V) (hf : Function.Surjective f)
    (he : ∀ x : A, ∀ u : U, f (x • u) = (a x) • f u)
    (hc : Nat.Coprime (Nat.card A) (Nat.card U))
    (hk : f.ker ≤ FixedPoints.subgroup A U) :
    Nat.card (commutatorAction A U) = 4 := by
  let _ := MulDistribMulAction.compHom V a
  let e := Theory.GroupAction.movingEquivOfFixedKernel f hf he hc hk
  rw [Nat.card_congr e.toEquiv,
    Theory.GroupAction.commutatorAction_eq_of_actor_surjective a ha]
  exact card_moving

abbrev NaturalV := Multiplicative (natural (Fin 7))
noncomputable instance : MulDistribMulAction (Equiv.Perm (Fin 7)) NaturalV :=
  Representation.BinaryGroupAction.action (naturalRepresentation (Fin 7))

/-- The same moving plane on the literal natural quotient used by block models. -/
theorem card_moving_natural : Nat.card (commutatorAction C NaturalV) = 4 := by
  let e : V ≃* NaturalV := (coreEquivNatural (Fin 7) (by decide)).toAddEquiv.toMultiplicative
  have he (c : C) (v : V) : e (c • v) = c • e v := by
    change Multiplicative.ofAdd ((coreEquivNatural (Fin 7) (by decide))
      (coreRepresentation (Fin 7) c.val v.toAdd)) =
      Multiplicative.ofAdd (naturalRepresentation (Fin 7) c.val
        ((coreEquivNatural (Fin 7) (by decide)) v.toAdd))
    exact congrArg Multiplicative.ofAdd (coreEquivNatural_equivariant (Fin 7) (by decide) c.val v.toAdd)
  rw [← Theory.GroupAction.commutatorAction_map_surjective e.toMonoidHom e.surjective he,
    card_map_of_injective (f := e.toMonoidHom) e.injective]
  exact card_moving
end BinaryPermutation.SevenCubic
