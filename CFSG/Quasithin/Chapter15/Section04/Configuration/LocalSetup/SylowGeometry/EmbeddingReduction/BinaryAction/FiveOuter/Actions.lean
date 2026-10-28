module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.ElementaryAbelian.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Tactic.IntervalCases

/-!
# The sections and fixers used by the degree-five Sylow-pair argument

The stabilizer of a binary subspace maps onto the linear groups on the
subspace and its quotient. When either section has dimension one, the kernel
of the action on the other section is a two-group. For dimensions two and
three, an order-nine subgroup has a proper nontrivial pointwise fixer.

These are the linear-algebra reductions for the L₅(2) case of the binary
outer-action argument in Aschbacher–Smith, printed pp.509–511 and 1164.
-/

@[expose] public section
open Subgroup BinaryLinear BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction.BinaryAction.FiveOuter

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

noncomputable def linearCoordinates [FiniteDimensional (ZMod 2) V] :
    BinaryLinear.GL V ≃* LinearGroup (Module.finrank (ZMod 2) V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm.trans
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv (Module.finBasis (ZMod 2) V).equivFun).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _))

theorem linear_card [FiniteDimensional (ZMod 2) V] :
    Nat.card (BinaryLinear.GL V) = ∏ i : Fin (Module.finrank (ZMod 2) V),
      (2 ^ Module.finrank (ZMod 2) V - 2 ^ (i : ℕ)) := by
  rw [Nat.card_congr (linearCoordinates (V := V)).toEquiv,
    ← Nat.card_congr (matrixEquivLinear (Module.finrank (ZMod 2) V)).toEquiv,
    Matrix.card_GL_field]
  simp

theorem nine_not_dvd_linear_card [FiniteDimensional (ZMod 2) V]
    (hdim : Module.finrank (ZMod 2) V < 4) : ¬ 9 ∣ Nat.card (BinaryLinear.GL V) := by
  rw [linear_card]
  generalize Module.finrank (ZMod 2) V = n at *
  interval_cases n <;> norm_num [Fin.prod_univ_succ]

theorem linear_eq_one_of_finrank_one [FiniteDimensional (ZMod 2) V]
    (hdim : Module.finrank (ZMod 2) V = 1) (g : BinaryLinear.GL V) : g = 1 := by
  have hc : Nat.card (BinaryLinear.GL V) = 1 := by
    rw [linear_card, hdim]
    norm_num [Fin.prod_univ_succ]
  exact (Nat.card_eq_one_iff_unique.mp hc).1.elim g 1

def restrictionAction (W : Submodule (ZMod 2) V) : parabolic W →* BinaryLinear.GL W where
  toFun r :=
    { toFun w := ⟨r.val w, (r.property w).mpr w.property⟩
      invFun w := ⟨r.val.symm w, ((parabolic W).inv_mem r.property w).mpr w.property⟩
      left_inv w := Subtype.ext (r.val.symm_apply_apply w)
      right_inv w := Subtype.ext (r.val.apply_symm_apply w)
      map_add' v w := Subtype.ext (r.val.map_add v w)
      map_smul' c w := Subtype.ext (r.val.map_smul c w) }
  map_one' := by apply LinearEquiv.ext; intro w; rfl
  map_mul' r s := by apply LinearEquiv.ext; intro w; rfl

private theorem map_eq_of_parabolic {W : Submodule (ZMod 2) V} {g : BinaryLinear.GL V}
    (hg : g ∈ parabolic W) : W.map g.toLinearMap = W := by
  apply le_antisymm
  · rintro x ⟨w, hw, rfl⟩
    exact (hg w).mpr hw
  · intro x hx
    exact ⟨g.symm x, (hg (g.symm x)).mp (by simpa using hx), g.apply_symm_apply x⟩

def quotientAction (W : Submodule (ZMod 2) V) :
    parabolic W →* BinaryLinear.GL (V ⧸ W) where
  toFun r := Submodule.Quotient.equiv W W r.val (by exact map_eq_of_parabolic r.property)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    induction x using Submodule.Quotient.induction_on with | _ x => rfl
  map_mul' r s := by
    apply LinearEquiv.ext
    intro x
    induction x using Submodule.Quotient.induction_on with | _ x => rfl

theorem restrictionAction_surjective [FiniteDimensional (ZMod 2) V]
    (W : Submodule (ZMod 2) V) : Function.Surjective (restrictionAction W) := by
  intro a
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq a
  have hgp : g ∈ parabolic W := by
    intro v
    constructor
    · intro hv
      obtain ⟨w, hw⟩ := a.surjective ⟨g v, hv⟩
      have hwv : (w : V) = v := g.injective ((hg w).symm.trans (congrArg Subtype.val hw))
      exact hwv ▸ w.property
    · intro hv
      rw [← hg ⟨v, hv⟩]
      exact (a ⟨v, hv⟩).property
  refine ⟨⟨g, hgp⟩, ?_⟩
  apply LinearEquiv.ext
  intro w
  exact Subtype.ext (hg w).symm

private def liftMap (W : Submodule (ZMod 2) V) (s : (V ⧸ W) →ₗ[ZMod 2] V)
    (a : BinaryLinear.GL (V ⧸ W)) : V →ₗ[ZMod 2] V :=
  LinearMap.id - s.comp W.mkQ + s.comp (a.toLinearMap.comp W.mkQ)

private theorem liftMap_apply (W : Submodule (ZMod 2) V) (s : (V ⧸ W) →ₗ[ZMod 2] V)
    (a : BinaryLinear.GL (V ⧸ W)) (x : V) :
    liftMap W s a x = x - s (W.mkQ x) + s (a (W.mkQ x)) := rfl

private theorem mkQ_liftMap (W : Submodule (ZMod 2) V) (s : (V ⧸ W) →ₗ[ZMod 2] V)
    (hs : ∀ x, W.mkQ (s x) = x) (a : BinaryLinear.GL (V ⧸ W)) (x : V) :
    W.mkQ (liftMap W s a x) = a (W.mkQ x) := by
  simp only [liftMap_apply, map_add, map_sub, hs, sub_self, zero_add]

private theorem liftMap_inv (W : Submodule (ZMod 2) V) (s : (V ⧸ W) →ₗ[ZMod 2] V)
    (hs : ∀ x, W.mkQ (s x) = x) (a : BinaryLinear.GL (V ⧸ W)) (x : V) :
    liftMap W s a.symm (liftMap W s a x) = x := by
  rw [liftMap_apply, mkQ_liftMap W s hs, liftMap_apply, a.symm_apply_apply]
  abel

theorem quotientAction_surjective (W : Submodule (ZMod 2) V) :
    Function.Surjective (quotientAction W) := by
  obtain ⟨s, hs⟩ := W.mkQ.exists_rightInverse_of_surjective W.range_mkQ
  have hs' (x : V ⧸ W) : W.mkQ (s x) = x := LinearMap.congr_fun hs x
  intro a
  let g : BinaryLinear.GL V :=
    { liftMap W s a with
      invFun := liftMap W s a.symm
      left_inv := liftMap_inv W s hs' a
      right_inv := liftMap_inv W s hs' a.symm }
  have hg : g ∈ parabolic W := by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.Quotient.mk_eq_zero]
    change W.mkQ (liftMap W s a v) = 0 ↔ W.mkQ v = 0
    rw [mkQ_liftMap W s hs', a.map_eq_zero_iff]
  refine ⟨⟨g, hg⟩, ?_⟩
  apply LinearEquiv.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => exact mkQ_liftMap W s hs' a x

theorem mem_radical_of_actions_eq_one (W : Submodule (ZMod 2) V) (g : parabolic W)
    (hr : restrictionAction W g = 1) (hq : quotientAction W g = 1) :
    g.val ∈ radical W := by
  constructor
  · intro w hw
    exact congrArg Subtype.val (LinearEquiv.congr_fun hr (⟨w, hw⟩ : W))
  · intro v
    exact (Submodule.Quotient.eq W).mp (LinearEquiv.congr_fun hq (Submodule.Quotient.mk v))

theorem quotientAction_kernel_two [FiniteDimensional (ZMod 2) V]
    (W : Submodule (ZMod 2) V) (hd : Module.finrank (ZMod 2) W = 1) :
    IsPGroup 2 (quotientAction W).ker := by
  apply ((radical_two W).comap_of_injective (parabolic W).subtype Subtype.val_injective).to_le
  intro g hg
  exact mem_radical_of_actions_eq_one W g (linear_eq_one_of_finrank_one hd _) hg

theorem restrictionAction_kernel_two [FiniteDimensional (ZMod 2) V]
    (W : Submodule (ZMod 2) V) (hd : Module.finrank (ZMod 2) (V ⧸ W) = 1) :
    IsPGroup 2 (restrictionAction W).ker := by
  apply ((radical_two W).comap_of_injective (parabolic W).subtype Subtype.val_injective).to_le
  intro g hg
  exact mem_radical_of_actions_eq_one W g hg (linear_eq_one_of_finrank_one hd _)

/-- Elements of the odd complement fixing the subspace pointwise. -/
def pointwiseFixer (R : Subgroup (BinaryLinear.GL V)) (W : Submodule (ZMod 2) V) :
    Subgroup R where
  carrier r := ∀ w ∈ W, r.val w = w
  one_mem' := by intro w hw; rfl
  mul_mem' := by intro r s hr hs w hw; change r.val (s.val w) = w; rw [hs w hw, hr w hw]
  inv_mem' := by
    intro r hr w hw
    change r.val.symm w = w
    apply r.val.injective
    simp [hr w hw]

private theorem pointwiseFixer_eq_ker (R : Subgroup (BinaryLinear.GL V))
    (W : Submodule (ZMod 2) V) (hR : R ≤ parabolic W) :
    pointwiseFixer R W = ((restrictionAction W).comp (inclusion hR)).ker := by
  ext r
  constructor
  · intro hr
    apply LinearEquiv.ext
    intro w
    exact Subtype.ext (hr w w.property)
  · intro hr w hw
    exact congrArg Subtype.val (LinearEquiv.congr_fun hr (⟨w, hw⟩ : W))

theorem pointwiseFixer_proper_nontrivial [FiniteDimensional (ZMod 2) V]
    (R : Subgroup (BinaryLinear.GL V)) (hcard : Nat.card R = 9)
    (W : Submodule (ZMod 2) V) (hWdim : Module.finrank (ZMod 2) W < 4)
    (hQdim : Module.finrank (ZMod 2) (V ⧸ W) < 4) (hR : R ≤ parabolic W) :
    pointwiseFixer R W ≠ ⊥ ∧ pointwiseFixer R W ≠ ⊤ := by
  have hthree : IsPGroup 3 R := IsPGroup.of_card (show Nat.card R = 3 ^ 2 from hcard)
  constructor
  · intro hb
    have hinj : Function.Injective ((restrictionAction W).comp (inclusion hR)) := by
      rw [← MonoidHom.ker_eq_bot_iff, ← pointwiseFixer_eq_ker, hb]
    have hdiv := Subgroup.card_dvd_of_injective _ hinj
    rw [hcard] at hdiv
    exact nine_not_dvd_linear_card hWdim hdiv
  · intro ht
    have hinj : Function.Injective ((quotientAction W).comp (inclusion hR)) := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      apply bot_unique
      intro r hr
      have hfix : ∀ w ∈ W, r.val w = w := (ht ▸ mem_top r : r ∈ pointwiseFixer R W)
      have hrad : r.val ∈ radical W := by
        refine ⟨hfix, ?_⟩
        intro v
        exact (Submodule.Quotient.eq W).mp (LinearEquiv.congr_fun hr (Submodule.Quotient.mk v))
      have hdis := hthree.disjoint_of_coprime (radical_two W) (by decide : Nat.Coprime 3 2)
      exact Subtype.ext ((Subgroup.disjoint_def.mp hdis) r.property hrad)
    have hdiv := Subgroup.card_dvd_of_injective _ hinj
    rw [hcard] at hdiv
    exact nine_not_dvd_linear_card hQdim hdiv

theorem pointwiseFixer_invariant (R : Subgroup (BinaryLinear.GL V))
    (W : Submodule (ZMod 2) V) (α : MulAut R) (g : BinaryLinear.GL V)
    (hg : g ∈ parabolic W)
    (he : ∀ r : R, (α r : BinaryLinear.GL V) = MulAut.conj g r)
    {r : R} (hr : r ∈ pointwiseFixer R W) : α r ∈ pointwiseFixer R W := by
  intro w hw
  rw [he]
  change g (r.val (g.symm w)) = w
  have hw' : g.symm w ∈ W := (hg (g.symm w)).mp (by simpa using hw)
  rw [hr _ hw']
  exact g.apply_symm_apply w

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.EmbeddingReduction.BinaryAction.FiveOuter
