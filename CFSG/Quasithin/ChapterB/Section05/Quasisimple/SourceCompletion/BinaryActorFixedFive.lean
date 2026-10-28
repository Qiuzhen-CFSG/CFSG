module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.BinaryActorMoved
public import Theory.Representation.BinaryFourQuinticFixed
public import Theory.Representation.BinaryOffender.DualDisplacement
public import Theory.Representation.GeneralLinearNatural

/-!
# Selecting the whole orthogonal moved module using a quintic fixed vector

In the binary degree-four B.5.1 alternatives, an order-five element fixes
no nonzero vector in the natural module, its dual, or any repeated natural
module. A nonzero fixed vector in the actual moved space therefore selects
the orthogonal row. The result retains both its six-dimensional central
quotient marking and the whole moved module: natural six-space or the
seven-dimensional augmentation core, with their actual actions.

The Chapter12 consumer supplies its original A6-fixed vector and a quintic
actor through the literal canonical quotient. Source: Aschbacher--Smith,
combined manuscript of 1 March 2004, 12.6.17, p.827, and B.5.1, pp.99--103.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion.BinaryActor
open scoped MatrixGroups

/-- Coordinates on the literal moved module and its central quotient. -/
@[expose] def OrthogonalMovedModel {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (C : Subgroup D) : Prop :=
  ∃ s : MovedSection ρ C,
    Nonempty (ActionEquiv (s.action.comp C.subtype) (alternatingNatural 8)) ∧
    (IsAlternatingNatural (s.space.toRepresentation.comp C.subtype) 8 ∨
      Nonempty (ActionEquiv (s.space.toRepresentation.comp C.subtype)
        (BinaryPermutation.alternatingCoreRepresentation (Fin 8)))) ∧
    (Module.finrank (ZMod 2) s.space.toSubmodule = 6 ∨
      Module.finrank (ZMod 2) s.space.toSubmodule = 7)

private theorem linear_four_faithful :
    Function.Injective (linearNatural BinaryField.two 4) := by
  intro x y h
  apply specialLinearNatural_injective 4
  apply LinearMap.ext
  intro v
  exact LinearMap.congr_fun h v
private theorem linear_four_fixed (x : SL(4,ZMod 2)) (hx : orderOf x = 5)
    (v : Fin 4 → ZMod 2) (hv : linearNatural BinaryField.two 4 x v = v) : v = 0 :=
  four_fixed_eq_zero_of_order_five _ linear_four_faithful (by change Module.finrank (ZMod 2) (Fin 4 → ZMod 2) = 4; simp) x hx v hv
private theorem dual_four_fixed (x : SL(4,ZMod 2)) (hx : orderOf x = 5)
    (v : Module.Dual (ZMod 2) (Fin 4 → ZMod 2))
    (hv : (linearNatural BinaryField.two 4).dual x v = v) : v = 0 :=
  four_fixed_eq_zero_of_order_five _ (faithful_dual _ linear_four_faithful)
    (by change Module.finrank (ZMod 2) (Module.Dual (ZMod 2) (Fin 4 → ZMod 2)) = 4; simp) x hx v hv
end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion.BinaryActor
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion.BinaryActor
open scoped MatrixGroups
variable {D W : Type*} [Group D] [Finite D]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W} {C : Subgroup D}

theorem orthogonal_of_quintic_fixed (s : MovedSection ρ C)
    (hc : ActionCase ρ C s 4) (x : C) (hx : orderOf x = 5)
    (z : s.space.toSubmodule) (hz : z ≠ 0)
    (hfix : s.space.toRepresentation x.val z = z) :
    Nonempty (ActionEquiv (s.action.comp C.subtype) (alternatingNatural 8)) ∧
      (IsAlternatingNatural (s.space.toRepresentation.comp C.subtype) 8 ∨
        Nonempty (ActionEquiv (s.space.toRepresentation.comp C.subtype)
          (BinaryPermutation.alternatingCoreRepresentation (Fin 8)))) ∧
      (Module.finrank (ZMod 2) s.space.toSubmodule = 6 ∨
        Module.finrank (ZMod 2) s.space.toSubmodule = 7) := by
  have hmodel := movedCase (Or.inl rfl) hc
  cases hmodel with
  | orthogonal _ a model dim => exact ⟨⟨a⟩,model,dim⟩
  | exterior hd _ _ _ => omega
  | natural a =>
    have ho : orderOf (a.groupEquiv x) = 5 := (a.groupEquiv.orderOf_eq x).trans hx
    have hf := a.intertwines x z
    change a.linearEquiv (s.space.toRepresentation x.val z) = _ at hf
    rw [hfix] at hf
    exact (hz (a.linearEquiv.map_eq_zero_iff.mp (linear_four_fixed _ ho _ hf.symm))).elim
  | naturalDual h =>
    obtain ⟨a⟩ := h
    have ho : orderOf (a.groupEquiv x) = 5 := (a.groupEquiv.orderOf_eq x).trans hx
    have hf := a.intertwines x z
    change a.linearEquiv (s.space.toRepresentation x.val z) = _ at hf
    rw [hfix] at hf
    have h1 := linear_four_fixed _ ho (a.linearEquiv z).1 (congrArg Prod.fst hf).symm
    have h2 := dual_four_fixed _ ho (a.linearEquiv z).2 (congrArg Prod.snd hf).symm
    exact (hz (a.linearEquiv.map_eq_zero_iff.mp (show a.linearEquiv z = 0 from Prod.ext h1 h2))).elim
  | repeatedNatural r _ _ h =>
    obtain ⟨a⟩ := h
    have ho : orderOf (a.groupEquiv x) = 5 := (a.groupEquiv.orderOf_eq x).trans hx
    have hf := a.intertwines x z
    change a.linearEquiv (s.space.toRepresentation x.val z) = _ at hf
    rw [hfix] at hf
    have he : a.linearEquiv z = 0 := by
      funext i
      exact linear_four_fixed _ ho _ (congrFun hf i).symm
    exact (hz (a.linearEquiv.map_eq_zero_iff.mp he)).elim
end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion.BinaryActor
