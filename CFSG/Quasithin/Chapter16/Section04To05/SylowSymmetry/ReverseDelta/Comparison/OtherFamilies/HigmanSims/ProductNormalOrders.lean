module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.Statements
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Basic
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Normal subgroup orders in the product HS row

The two-residual of C₂ × Aut(A₆) is the actual subgroup 1 × Inn(A₆).
Indeed, this subgroup is perfect and normal, and its quotient has order eight:
Inn(A₆) has index four in Aut(A₆). Transport along a group isomorphism
therefore identifies the residual with A₆. Simplicity forces every nonsolvable
normal subgroup of the residual to have order 360, hence order divisible by nine.

This is the intrinsic product-row input to the comparison of inner and outer
involution centralizers in Aschbacher–Smith, combined manuscript (1 March 2004),
16.1.5(10), printed p.1172, and the proof of 16.4.11(2), printed p.1193.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims

private theorem perfect_twoPerfect {H : Type*} [Group H] [Finite H]
    [Group.IsPerfect H] : IsPPerfect 2 H := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (H ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (H ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro x _
  exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)

private noncomputable def productInnerEquiv :
    (⊥ : Subgroup C2).prod AlternatingSix.ShadowLocal.inner ≃* A6 :=
  (show (⊥ : Subgroup C2).prod AlternatingSix.ShadowLocal.inner ≃*
      AlternatingSix.ShadowLocal.inner from
    { toFun := fun x => ⟨x.val.2, x.property.2⟩
      invFun := fun x => ⟨(1, x), ⟨rfl, x.property⟩⟩
      left_inv := fun x => Subtype.ext (Prod.ext (mem_bot.mp x.property.1).symm rfl)
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }).trans AlternatingSix.ShadowLocal.innerEquiv.symm

/-- The two-residual is the embedded inner A₆ factor, with trivial C₂ coordinate. -/
theorem hs_product_twoResidual_eq :
    pResidual 2 (C2 × MulAut A6) =
      (⊥ : Subgroup C2).prod AlternatingSix.ShadowLocal.inner := by
  let J := (⊥ : Subgroup C2).prod AlternatingSix.ShadowLocal.inner
  let : Group.IsPerfect A6 := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect J := Group.IsPerfect.ofSurjective
    (f := productInnerEquiv.symm.toMonoidHom) productInnerEquiv.symm.surjective
  apply pResidual_eq_of_isPPerfect J perfect_twoPerfect
  apply IsPGroup.of_card (n := 3)
  change J.index = 2 ^ 3
  rw [index_prod, index_bot, AlternatingSix.ShadowLocal.inner_index]
  norm_num [C2]

/-- An actual product-row isomorphism identifies the two-residual with A₆. -/
noncomputable def hsProductResidualEquiv {C : Type*} [Group C]
    (e : C ≃* C2 × MulAut A6) : pResidual 2 C ≃* A6 :=
  (e.subgroupMap (pResidual 2 C)).trans
    ((MulEquiv.subgroupCongr ((map_pResidual 2 e).trans hs_product_twoResidual_eq)).trans
      productInnerEquiv)

/-- A nonsolvable subgroup normal in the product-row two-residual has order 360. -/
theorem hs_product_residual_normal_card {C : Type*} [Group C] [Finite C]
    (e : C ≃* C2 × MulAut A6) (N : Subgroup (pResidual 2 C))
    (hN : N.Normal) (hns : ¬ Group.IsSolvable N) : Nat.card N = 360 := by
  let f := hsProductResidualEquiv e
  let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (pResidual 2 C) := (MulEquiv.isSimpleGroup_congr f).mpr inferInstance
  rcases hN.eq_bot_or_eq_top with h | h
  · subst N
    exact (hns inferInstance).elim
  · rw [h, Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_congr f.toEquiv]
    exact AlternatingSix.ShadowLocal.card_A6

/-- The product-row normal-order bound used in the HS centralizer comparison. -/
theorem hs_product_residual_normal_nine_dvd {C : Type*} [Group C] [Finite C]
    (e : C ≃* C2 × MulAut A6) (N : Subgroup (pResidual 2 C))
    (hN : N.Normal) (hns : ¬ Group.IsSolvable N) : 9 ∣ Nat.card N := by
  rw [hs_product_residual_normal_card e N hN hns]
  decide

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies
