module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The three-point permutation model of `SL₂(2)`

The special linear group over the field with two elements is isomorphic to
`S₃`. Its projective action is faithful because its center is trivial. The
projective line has three points and the group has order six, so the faithful
action fills the permutation group. A choice of numbering identifies it with
the permutations of `Fin 3`.

The cardinality and projective-line equivalence are public because the
order-six recognition argument in Stellmacher (1.6) uses that exact line.
The construction also supplies an intrinsic model for local wreath-product
calculations. This proof is extracted from
`Stellmacher/SectionOne/CThreeCtwoSLTwo.lean`; its ingredients are Mathlib's
projective-action kernel and finite-field cardinality theorems.
-/

namespace SLTwoPermThree

private abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
private abbrev PLine2 := Projectivization (ZMod 2) (Fin 2 → ZMod 2)

private theorem sl2_center_eq_bot :
    Subgroup.center SL2 = ⊥ := by
  ext A
  constructor
  · intro hA
    rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
    obtain ⟨r, hr, hrA⟩ := hA
    have hrone : r = 1 := by
      have hr' : r ^ 2 = 1 := by simpa using hr
      have h : ∀ x : ZMod 2, x ^ 2 = 1 → x = 1 := by decide +kernel
      exact h r hr'
    subst r
    have hAone : A = 1 := by
      apply Subtype.ext
      rw [← hrA]
      ext i j
      simp [Matrix.scalar_apply]
    simp [hAone]
  · intro hA
    have hAone : A = 1 := hA
    subst A
    exact Subgroup.one_mem _

private theorem sl2_projective_action_injective :
    Function.Injective
      (MulAction.toPermHom SL2 PLine2) := by
  rw [← MonoidHom.ker_eq_bot_iff,
    Projectivization.SL_mulAction_ker]
  exact sl2_center_eq_bot

private theorem sl2_card : Nat.card SL2 = 6 := by
  let toSL : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) →* SL2 :=
    { toFun := fun a => ⟨a.1, by
        have hunit : IsUnit a.1.det :=
          a.1.isUnit_iff_isUnit_det.mp a.isUnit
        have h : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide +kernel
        exact h _ hunit.ne_zero⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  have htoSLinj : Function.Injective toSL := by
    intro a b hab
    apply Units.ext
    exact congrArg Subtype.val hab
  have htoSLsurj : Function.Surjective toSL := by
    intro a
    refine ⟨(a : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)), ?_⟩
    exact Subtype.ext rfl
  let e : Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) ≃* SL2 :=
    MulEquiv.ofBijective toSL ⟨htoSLinj, htoSLsurj⟩
  calc
    Nat.card SL2 = Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) :=
      Nat.card_congr e.symm.toEquiv
    _ = 6 := by
      rw [Matrix.card_GL_field]
      norm_num [Fin.prod_univ_succ]

/-- The projective line over the field with two elements has three points. -/
public theorem projectiveLineTwo_card :
    Nat.card (Projectivization (ZMod 2) (Fin 2 → ZMod 2)) = 3 := by
  rw [Projectivization.card_of_finrank_two]
  · norm_num
  · exact Module.finrank_fin_fun (R := ZMod 2)

/-- The faithful projective action of `SL₂(2)` is the full permutation group. -/
public noncomputable def sl2EquivPermProjectiveLine :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ≃*
      Equiv.Perm (Projectivization (ZMod 2) (Fin 2 → ZMod 2)) := by
  let f := MulAction.toPermHom SL2 PLine2
  refine MulEquiv.ofBijective f ?_
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨sl2_projective_action_injective, ?_⟩
  rw [sl2_card, Nat.card_perm, projectiveLineTwo_card]
  norm_num [Nat.factorial]

/-- The existing projective-line action identifies `SL₂(2)` with `S₃`. -/
public theorem sl2Two_equiv_perm_three :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ≃* Equiv.Perm (Fin 3)) := by
  classical
  let : Fintype PLine2 := Fintype.ofFinite PLine2
  let e : PLine2 ≃ Fin 3 := Fintype.equivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_fin]
    exact projectiveLineTwo_card)
  exact ⟨sl2EquivPermProjectiveLine.trans e.permCongrHom⟩

end SLTwoPermThree
