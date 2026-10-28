module
public import Theory.Representation.IrreducibleSimpleFaithful
public import Theory.SpecificGroups.Janko4.Model.Center
public import Theory.Mathieu.M24.Properties.Order
public import Theory.Mathieu.M24.Properties.Simplicity
public import Theory.Representation.BinaryNaturalAutomorphisms
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The sporadic exclusions in binary degree six

A faithful binary action of degree six makes the group order divide
|GL₆(2)|. The known order of M₂₄ violates this divisibility. For J₄,
the certified element of order 37 already suffices. Centerlessness and
the quasisimplicity inherited from a containing component supply its
simplicity; no independent J₄ simplicity certification is needed.

These are the two sporadic action exclusions in Aschbacher--Smith,
12.5.3, printed p.819. Their ambient application retains the actual
two-core quotient and conjugation on the marked exterior six-space.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Representation
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

theorem card_dvd_binary_six_of_faithful
    (ρ : Representation (ZMod 2) H W) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) W = 6) :
    Nat.card H ∣ 20158709760 := by
  let b : Module.Basis (Fin 6) (ZMod 2) W := hd ▸ Module.finBasis (ZMod 2) W
  let e := Matrix.GeneralLinearGroup.toLin' b
  let f := e.symm.toMonoidHom.comp ρ.asGroupHom
  have hi : Function.Injective f := e.symm.injective.comp (by
    intro x y he
    exact hf (congrArg Units.val he))
  have hc : Nat.card (Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) = 20158709760 := by
    rw [Matrix.card_GL_field, ZMod.card]
    norm_num [Fin.prod_univ_succ]
  exact hc ▸ card_dvd_of_injective f hi

theorem no_irreducible_mathieu_six (ρ : Representation (ZMod 2) Sporadic.Mathieu.M24 W)
    [IsIrreducible ρ] (hd : Module.finrank (ZMod 2) W = 6) : False := by
  let := Sporadic.Mathieu.m24_isSimpleGroup
  have hf := injective_of_simple_of_irreducible_of_one_lt_finrank ρ (by omega)
  have hh := card_dvd_binary_six_of_faithful ρ hf hd
  rw [Sporadic.Mathieu.m24_order] at hh
  norm_num at hh

/-- Only inherited quasisimplicity is needed; no global J₄ simplicity certification. -/
theorem no_irreducible_janko_six [IsQuasisimple Janko4.Model]
    (ρ : Representation (ZMod 2) Janko4.Model W)
    [IsIrreducible ρ] (hd : Module.finrank (ZMod 2) W = 6) : False := by
  let : IsSimpleGroup (Janko4.Model ⧸ center Janko4.Model) := IsQuasisimple.simple
  let : IsSimpleGroup Janko4.Model :=
    ((QuotientGroup.quotientMulEquivOfEq Janko4.model_center_eq_bot).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  have hf := injective_of_simple_of_irreducible_of_one_lt_finrank ρ (by omega)
  have hh : 37 ∣ 20158709760 := (Janko4.orderOf_a_mul_b ▸
    orderOf_dvd_natCard (Janko4.a * Janko4.b)).trans
      (card_dvd_binary_six_of_faithful ρ hf hd)
  norm_num at hh
end Representation
