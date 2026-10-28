module
public import Theory.SpecificGroups.ProjectiveLinear.EvenOrderFour
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.ElementaryAbelian.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Order four in full binary linear groups

The existing order-four element of PSL3(2) acts on a three-dimensional summand
and identically on its complement. The explicit block action is injective,
so the resulting element has the same order in GL(V). Its cyclic two-subgroup
lies in a Sylow subgroup, excluding elementary Sylow two-subgroups.

Source application: Aschbacher--Smith G.10.15(3), printed pp.362--363,
noncentral constituent-kernel branch.
-/

@[expose] public noncomputable section
open Subgroup Module
open scoped MatrixGroups
namespace BinaryLinear

/-- Every binary linear group of dimension at least three has an actual
element of order four, embedded on a three-dimensional summand. -/
theorem exists_order_four_of_finrank_ge_three {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (hd : 3 ≤ finrank (ZMod 2) V) :
    ∃ a : LinearMap.GeneralLinearGroup (ZMod 2) V, orderOf a = 4 := by
  classical
  let W := Fin 3 → ZMod 2
  let D := Fin (finrank (ZMod 2) V - 3) → ZMod 2
  let e : (W × D) ≃ₗ[ZMod 2] V := LinearEquiv.ofFinrankEq _ _ (by
    simp only [W, D, Module.finrank_prod, Module.finrank_pi, Fintype.card_fin]
    omega)
  let f : BinaryLinear.GL W →* BinaryLinear.GL V :=
    { toFun := fun a => (e.symm.trans (a.prodCongr (LinearEquiv.refl (ZMod 2) D))).trans e
      map_one' := by ext v; simp
      map_mul' a b := by ext v; simp }
  have hf : Function.Injective f := by
    intro a b hab
    apply LinearEquiv.ext
    intro w
    have he := congrArg (fun c : BinaryLinear.GL V => (e.symm (c (e (w,0)))).1) hab
    simpa [f] using he
  obtain ⟨a,ha⟩ := Matrix.ProjectiveSpecialLinearGroup.exists_order_four_of_char_two (F:=ZMod 2)
  let c : BinaryLinear.GL W := BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0<3) a
  have hc : orderOf c = 4 := (MulEquiv.orderOf_eq _ a).trans ha
  let q := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V
  refine ⟨q.symm (f c),?_⟩
  rw [MulEquiv.orderOf_eq, orderOf_injective f hf, hc]

/-- Full binary linear groups in dimension at least three cannot have
elementary abelian Sylow two-subgroups. -/
theorem not_elementary_sylow_of_finrank_ge_three
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [Finite (LinearMap.GeneralLinearGroup (ZMod 2) V)]
    (hd : 3 ≤ finrank (ZMod 2) V)
    (he : ∀ P : Sylow 2 (LinearMap.GeneralLinearGroup (ZMod 2) V), IsElementaryAbelian 2 P) : False := by
  obtain ⟨a,ha⟩ := exists_order_four_of_finrank_ge_three hd
  have hp : IsPGroup 2 (zpowers a) := IsPGroup.of_card (n:=2) (by
    rw [Nat.card_zpowers,ha]
    decide)
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  let : IsElementaryAbelian 2 P := he P
  have hh := elemPow_eq_one_of_isElementaryAbelian (p:=2) a (hP (mem_zpowers a))
  have hdvd : 4 ∣ 2 := ha ▸ orderOf_dvd_of_pow_eq_one hh
  norm_num at hdvd

end BinaryLinear
