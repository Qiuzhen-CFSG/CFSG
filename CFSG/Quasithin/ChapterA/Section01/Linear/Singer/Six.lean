module

public import CFSG.Quasithin.ChapterA.Section01.Linear.Singer.Defs
public import CFSG.Quasithin.ChapterA.Section01.Linear.Dickson
public import CFSG.Quasithin.ChapterA.Section01.Linear.Singer.Six.Fitting
public import CFSG.Quasithin.ChapterA.Section01.Linear.Singer.Six.Dickson
public import CFSG.Quasithin.ChapterA.Section01.Linear.Singer.Six.FieldRealization
public import CFSG.Quasithin.ChapterA.Section01.Linear.Singer.FixedVectors

/-!
# The exceptional six-dimensional Singer reduction

For A.1.12 in dimension six, the Sylow calculation constructs W of order
seven and the fixed-vector input makes W centralize F(Y). A genuine
embedding of the full linear centralizer of W in GL₂(8) then gives
|C_Y(W)| ≤ 63 by Dickson. Since |X| = 63, this proves C_Y(W) = X,
W = O₇(Y), and normality of X inside Y.

The field realization constructs these scalars on the actual V. The final
theorem below supplies that embedding and derives the fixed-vector input
from oddness, completing the dimension-six branch.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.1.12, printed p.22.
-/

open Subgroup
namespace CFSG.Quasithin.ChapterA.Singer.Six

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Restrict a faithful realization of the full linear centralizer to the
centralizer inside the odd overgroup, and apply the proved Dickson bound. -/
public theorem centralizer_card_le_of_embedding
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 8)
    (hn : Module.finrank (ZMod 2) V = 6)
    (Y W : Subgroup (V ≃ₗ[ZMod 2] V)) (hWY : W ≤ Y) (hodd : Odd (Nat.card Y))
    (ρ : centralizer (W : Set (V ≃ₗ[ZMod 2] V)) →*
      Matrix.GeneralLinearGroup (Fin 2) F) (hρ : Function.Injective ρ) :
    Nat.card (centralizer (W.subgroupOf Y : Set Y)) ≤ 63 := by
  let : Finite (V ≃ₗ[ZMod 2] V) := Nat.finite_of_card_ne_zero (by
    rw [card_linearGroup hn]; decide)
  let C := centralizer (W.subgroupOf Y : Set Y)
  let i : C →* centralizer (W : Set (V ≃ₗ[ZMod 2] V)) :=
    { toFun := fun c => ⟨c.val.val, by
        apply mem_centralizer_iff.mpr
        intro w hw
        exact congrArg (fun y : Y => (y : V ≃ₗ[ZMod 2] V))
          (mem_centralizer_iff.mp c.property ⟨w, hWY hw⟩ hw)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hi : Function.Injective i := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c : centralizer (W : Set (V ≃ₗ[ZMod 2] V)) =>
      (c : V ≃ₗ[ZMod 2] V)) hab
  let j := ρ.comp i
  have hj : Function.Injective j := hρ.comp hi
  have hcard : Nat.card C = Nat.card j.range := Nat.card_congr (j.ofInjective hj).toEquiv
  have hCodd : Odd (Nat.card C) := hodd.of_dvd_nat C.card_subgroup_dvd_card
  change Nat.card C ≤ 63
  rw [hcard] at hCodd ⊢
  exact odd_gl_eight_card_le_sixty_three hF j.range hCodd

/-- Complete the group-theoretic argument from a genuine GL₂(8) embedding.
The model construction is deliberately retained as an explicit premise. -/
public theorem seven_core_and_normal_of_centralizer_embedding
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 8)
    (hn : Module.finrank (ZMod 2) V = 6)
    (X Y W : Subgroup (V ≃ₗ[ZMod 2] V)) [IsCyclic X]
    (hreg : LinearGroup.IsRegularOnNonzero X) (hXY : X ≤ Y)
    (hWX : W ≤ X) (hW : Nat.card W = 7)
    (hodd : Odd (Nat.card Y)) (hsolv : Group.IsSolvable Y)
    (hfp : PrimeFixedPointCentralization Y)
    (ρ : centralizer (W : Set (V ≃ₗ[ZMod 2] V)) →*
      Matrix.GeneralLinearGroup (Fin 2) F) (hρ : Function.Injective ρ) :
    centralizer (W.subgroupOf Y : Set Y) = X.subgroupOf Y ∧
      W.subgroupOf Y = pCore 7 Y ∧ (X.subgroupOf Y).Normal := by
  have hbound := centralizer_card_le_of_embedding hF hn Y W (hWX.trans hXY) hodd ρ hρ
  have hCW := centralizer_eq_of_card_le hn X Y W hreg hXY hWX hbound
  exact ⟨hCW, seven_core_and_normal_of_centralizer_eq hn X Y W hreg hXY hWX hW
    hsolv hfp hCW⟩

/-- The six-dimensional branch of A.1.12. Both the field realization and
the fixed-vector input are discharged from the original action hypotheses. -/
public theorem normal_of_finrank_eq_six
    (hn : Module.finrank (ZMod 2) V = 6)
    (X Y : Subgroup (V ≃ₗ[ZMod 2] V)) [IsCyclic X]
    (hreg : LinearGroup.IsRegularOnNonzero X) (hXY : X ≤ Y)
    (hodd : Odd (Nat.card Y)) (hsolv : Group.IsSolvable Y) :
    (X.subgroupOf Y).Normal := by
  obtain ⟨W, hWX, hW⟩ := exists_seven_subgroup hn hreg
  obtain ⟨F, hField, hFinite, hF, ρ, hρ⟩ :=
    exists_centralizer_embedding hn X W hreg hWX hW
  let := hField
  let := hFinite
  exact (seven_core_and_normal_of_centralizer_embedding hF hn X Y W hreg hXY hWX hW
    hodd hsolv (primeFixedPointCentralization_of_odd Y hodd) ρ hρ).2.2

end CFSG.Quasithin.ChapterA.Singer.Six
