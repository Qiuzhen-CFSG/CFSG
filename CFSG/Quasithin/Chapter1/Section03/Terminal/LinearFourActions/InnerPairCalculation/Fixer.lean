module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.ElementaryAbelian.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Tactic.IntervalCases

/-!
# A nontrivial proper fixer on an invariant binary subspace

For an order-nine subgroup of GL₄(2), the action on any proper nonzero
invariant subspace has a nontrivial kernel, since GLₖ(2) has no subgroup
of order nine for k < 4. That kernel is proper: otherwise the action on
the quotient is faithful, as its kernel lies in a two-group radical.
The same order argument excludes this possibility on the quotient.
Conjugation preserving the subspace preserves its pointwise fixer.

This supplies the invariant subgroup in the inner-action calculation for
Aschbacher–Smith, proof of Lemma 1.3.9, printed p.514.
-/

@[expose] public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.InnerPairCalculation

private theorem linear_card (V : Type*) [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] :
    Nat.card (BinaryLinear.GL V) = ∏ i : Fin (Module.finrank (ZMod 2) V),
      (2 ^ Module.finrank (ZMod 2) V - 2 ^ (i : ℕ)) := by
  let e := (Module.finBasis (ZMod 2) V).equivFun
  let f : BinaryLinear.GL V ≃* LinearGroup (Module.finrank (ZMod 2) V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm.trans
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv e).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _))
  rw [Nat.card_congr f.toEquiv,
    ← Nat.card_congr (matrixEquivLinear (Module.finrank (ZMod 2) V)).toEquiv,
    Matrix.card_GL_field]
  simp

private theorem nine_not_dvd_linear_card (V : Type*) [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (hdim : Module.finrank (ZMod 2) V < 4) :
    ¬ 9 ∣ Nat.card (BinaryLinear.GL V) := by
  rw [linear_card]
  generalize Module.finrank (ZMod 2) V = n at *
  interval_cases n <;> norm_num [Fin.prod_univ_succ]

private def restrictionAction (R : Subgroup (BinaryLinear.GL (Space 4)))
    (W : Submodule (ZMod 2) (Space 4)) (hR : R ≤ parabolic W) : R →* BinaryLinear.GL W where
  toFun r :=
    { toFun w := ⟨r.val w, (hR r.property w).mpr w.property⟩
      invFun w := ⟨r.val.symm w, (hR (R.inv_mem r.property) w).mpr w.property⟩
      left_inv w := Subtype.ext (r.val.symm_apply_apply w)
      right_inv w := Subtype.ext (r.val.apply_symm_apply w)
      map_add' v w := Subtype.ext (r.val.map_add v w)
      map_smul' c w := Subtype.ext (r.val.map_smul c w) }
  map_one' := by apply LinearEquiv.ext; intro w; rfl
  map_mul' r s := by apply LinearEquiv.ext; intro w; rfl

private theorem map_eq_of_parabolic {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {W : Submodule (ZMod 2) V} {g : BinaryLinear.GL V} (hg : g ∈ parabolic W) :
    W.map g.toLinearMap = W := by
  apply le_antisymm
  · rintro x ⟨w, hw, rfl⟩
    exact (hg w).mpr hw
  · intro x hx
    exact ⟨g.symm x, (hg (g.symm x)).mp (by simpa using hx), g.apply_symm_apply x⟩

private def quotientAction (R : Subgroup (BinaryLinear.GL (Space 4)))
    (W : Submodule (ZMod 2) (Space 4)) (hR : R ≤ parabolic W) :
    R →* BinaryLinear.GL ((Space 4) ⧸ W) where
  toFun r := Submodule.Quotient.equiv W W r.val (map_eq_of_parabolic (hR r.property))
  map_one' := by
    apply LinearEquiv.ext
    intro x
    induction x using Submodule.Quotient.induction_on with | _ x => rfl
  map_mul' r s := by
    apply LinearEquiv.ext
    intro x
    induction x using Submodule.Quotient.induction_on with | _ x => rfl

/-- Elements of the complement fixing a subspace pointwise. -/
def pointwiseFixer (R : Subgroup (BinaryLinear.GL (Space 4)))
    (W : Submodule (ZMod 2) (Space 4)) : Subgroup R where
  carrier r := ∀ w ∈ W, r.val w = w
  one_mem' := by intro w hw; rfl
  mul_mem' := by intro r s hr hs w hw; change r.val (s.val w) = w; rw [hs w hw, hr w hw]
  inv_mem' := by
    intro r hr w hw
    change r.val.symm w = w
    apply r.val.injective
    simp [hr w hw]

private theorem pointwiseFixer_eq_ker (R : Subgroup (BinaryLinear.GL (Space 4)))
    (W : Submodule (ZMod 2) (Space 4)) (hR : R ≤ parabolic W) :
    pointwiseFixer R W = (restrictionAction R W hR).ker := by
  ext r
  constructor
  · intro hr
    apply LinearEquiv.ext
    intro w
    exact Subtype.ext (hr w w.property)
  · intro hr w hw
    exact congrArg Subtype.val (LinearEquiv.congr_fun hr (⟨w, hw⟩ : W))

/-- An order-nine subgroup of GL₄(2) has a proper nonzero pointwise fixer
on each proper nonzero invariant subspace. -/
theorem pointwiseFixer_proper_nontrivial (R : Subgroup (BinaryLinear.GL (Space 4)))
    (hcard : Nat.card R = 9) (W : Submodule (ZMod 2) (Space 4))
    (hW0 : W ≠ ⊥) (hW1 : W ≠ ⊤) (hR : R ≤ parabolic W) :
    pointwiseFixer R W ≠ ⊥ ∧ pointwiseFixer R W ≠ ⊤ := by
  have hd : Module.finrank (ZMod 2) (Space 4) = 4 := by simp [Space]
  have hWdim : Module.finrank (ZMod 2) W < 4 := by
    simpa only [hd] using Submodule.finrank_lt hW1
  have hQdim : Module.finrank (ZMod 2) ((Space 4) ⧸ W) < 4 := by
    have hsum := W.finrank_quotient_add_finrank
    have hpos : 0 < Module.finrank (ZMod 2) W := by
      have hn : Module.finrank (ZMod 2) W ≠ 0 := by
        intro hz
        exact hW0 (Submodule.finrank_eq_zero.mp hz)
      omega
    omega
  have hthree : IsPGroup 3 R := IsPGroup.of_card (show Nat.card R = 3 ^ 2 from hcard)
  constructor
  · intro hb
    have hinj : Function.Injective (restrictionAction R W hR) := by
      rw [← MonoidHom.ker_eq_bot_iff, ← pointwiseFixer_eq_ker, hb]
    have hdiv := Subgroup.card_dvd_of_injective (restrictionAction R W hR) hinj
    rw [hcard] at hdiv
    exact nine_not_dvd_linear_card W hWdim hdiv
  · intro ht
    have hinj : Function.Injective (quotientAction R W hR) := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      apply bot_unique
      intro r hr
      have hfix : ∀ w ∈ W, r.val w = w := (ht ▸ mem_top r : r ∈ pointwiseFixer R W)
      have hrad : r.val ∈ radical W := by
        refine ⟨hfix, ?_⟩
        intro v
        have hv := LinearEquiv.congr_fun hr (Submodule.Quotient.mk v)
        change (Submodule.Quotient.mk (r.val v) : (Space 4) ⧸ W) = Submodule.Quotient.mk v at hv
        exact (Submodule.Quotient.eq W).mp hv
      have hdis := hthree.disjoint_of_coprime (radical_two W) (by decide : Nat.Coprime 3 2)
      exact Subtype.ext ((Subgroup.disjoint_def.mp hdis) r.property hrad)
    have hdiv := Subgroup.card_dvd_of_injective (quotientAction R W hR) hinj
    rw [hcard] at hdiv
    exact nine_not_dvd_linear_card ((Space 4) ⧸ W) hQdim hdiv

/-- An inner automorphism preserving the subspace preserves its pointwise fixer. -/
theorem pointwiseFixer_invariant (R : Subgroup (BinaryLinear.GL (Space 4)))
    (W : Submodule (ZMod 2) (Space 4)) (α : MulAut R)
    (g : BinaryLinear.GL (Space 4)) (hg : g ∈ parabolic W)
    (he : ∀ r : R, (α r : BinaryLinear.GL (Space 4)) = MulAut.conj g r)
    {r : R} (hr : r ∈ pointwiseFixer R W) : α r ∈ pointwiseFixer R W := by
  intro w hw
  rw [he]
  change g (r.val (g.symm w)) = w
  have hw' : g.symm w ∈ W := (hg (g.symm w)).mp (by simpa using hw)
  rw [hr _ hw']
  exact g.apply_symm_apply w

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.InnerPairCalculation
