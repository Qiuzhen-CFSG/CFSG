module

public import Theory.SpecificGroups.ReeTwo.FixingModelFirstCoreBasic

/-!
# Collected coordinates for fixing census action two

The three polynomial actions are checked against the root presentation and
composition. They supply efficient, kernel-checked arithmetic for both choices
of the actor's fourth power.

Source: Shinoda (1975), (2.3), through `Core` and the row indexed by two of
`FixingActionRepresentatives`.
-/

@[expose] public section
namespace ReeTwo.FixingModel.Two
open Core.FixingActionCensus

def action1 (x : Core) : Core where
  b0 := x.b0 + x.b1 + x.b4
  b1 := x.b1 + x.b3 + x.b4
  b2 := x.b0 + x.b1 + x.b2 + x.b3 + x.b4
  b3 := x.b0 + x.b1 + x.b3
  b4 := x.b0 + x.b3 + x.b4
  b5 := x.b1 + x.b3 + x.b1 * x.b3 + x.b4 + x.b1 * x.b4 + x.b2 * x.b4 + x.b3 * x.b4 + x.b5 + x.b6 + x.b8
  b6 := x.b1 + x.b0 * x.b1 + x.b3 + x.b0 * x.b3 + x.b1 * x.b3 + x.b2 * x.b3 + x.b0 * x.b4 + x.b2 * x.b4 + x.b3 * x.b4 + x.b6 + x.b7 + x.b8
  b7 := x.b0 * x.b1 + x.b0 * x.b2 + x.b1 * x.b2 + x.b3 + x.b1 * x.b3 + x.b0 * x.b4 + x.b1 * x.b4 + x.b3 * x.b4 + x.b5 + x.b6 + x.b7
  b8 := x.b1 + x.b0 * x.b1 + x.b0 * x.b2 + x.b3 + x.b0 * x.b3 + x.b1 * x.b3 + x.b5 + x.b7 + x.b8
  b9 := x.b1 + x.b0 * x.b2 + x.b1 * x.b2 + x.b0 * x.b1 * x.b3 + x.b0 * x.b4 + x.b0 * x.b1 * x.b4 + x.b5 + x.b6 + x.b7 + x.b8 + x.b9

def action2 (x : Core) : Core where
  b0 := x.b4
  b1 := x.b3
  b2 := x.b2
  b3 := x.b1
  b4 := x.b0
  b5 := x.b4 + x.b1 * x.b4 + x.b2 * x.b4 + x.b8
  b6 := x.b3 + x.b2 * x.b3 + x.b0 * x.b4 + x.b1 * x.b4 + x.b7
  b7 := x.b1 + x.b1 * x.b2 + x.b0 * x.b3 + x.b0 * x.b4 + x.b6
  b8 := x.b0 + x.b0 * x.b2 + x.b0 * x.b3 + x.b5
  b9 := x.b0 * x.b3 + x.b1 * x.b3 + x.b0 * x.b4 + x.b1 * x.b4 + x.b0 * x.b1 * x.b4 + x.b0 * x.b3 * x.b4 + x.b9

def action3 (x : Core) : Core where
  b0 := x.b0 + x.b3 + x.b4
  b1 := x.b0 + x.b1 + x.b3
  b2 := x.b0 + x.b1 + x.b2 + x.b3 + x.b4
  b3 := x.b1 + x.b3 + x.b4
  b4 := x.b0 + x.b1 + x.b4
  b5 := x.b1 + x.b0 * x.b1 + x.b1 * x.b3 + x.b2 * x.b3 + x.b4 + x.b0 * x.b4 + x.b2 * x.b4 + x.b5 + x.b7 + x.b8
  b6 := x.b0 + x.b0 * x.b1 + x.b1 * x.b3 + x.b2 * x.b3 + x.b0 * x.b4 + x.b3 * x.b4 + x.b5 + x.b6 + x.b7
  b7 := x.b0 * x.b1 + x.b1 * x.b2 + x.b3 + x.b1 * x.b3 + x.b4 + x.b0 * x.b4 + x.b3 * x.b4 + x.b6 + x.b7 + x.b8
  b8 := x.b0 + x.b0 * x.b2 + x.b1 * x.b2 + x.b3 + x.b1 * x.b3 + x.b4 + x.b0 * x.b4 + x.b3 * x.b4 + x.b5 + x.b6 + x.b8
  b9 := x.b0 + x.b1 + x.b0 * x.b2 + x.b1 * x.b2 + x.b0 * x.b3 + x.b1 * x.b3 + x.b4 + x.b1 * x.b4 + x.b0 * x.b1 * x.b4 + x.b1 * x.b3 * x.b4 + x.b5 + x.b6 + x.b7 + x.b8 + x.b9

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
private def actionHom : Core →* Core where
  toFun := action1
  map_one' := by decide +kernel
  map_mul' x y := by
    change action1 (Core.mul x y) = Core.mul (action1 x) (action1 y)
    apply Core.ext <;> simp only [action1, Core.mul] <;> ring_nf
    all_goals reduce_mod_char
    all_goals simp only [show ∀ z : ZMod 2, z ^ 2 = z from by decide]
    all_goals ring_nf
    all_goals reduce_mod_char

theorem action1_eq (x : Core) : action1 x = representative 2 x := by
  have h : actionHom = (representative 2).toMonoidHom := by
    apply Core.hom_ext
    exact (by decide +kernel : ∀ i : CoreRoot,
      actionHom (Core.root i) = representative 2 (Core.root i))
  exact DFunLike.congr_fun h x

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem action2_eq (x : Core) : action2 x = action1 (action1 x) := by
  apply Core.ext <;> simp only [action2, action1, action1] <;> ring_nf
  all_goals reduce_mod_char
  all_goals simp only [show ∀ z : ZMod 2, z ^ 2 = z from by decide,
      show ∀ z : ZMod 2, z ^ 3 = z from by decide]
  all_goals ring_nf
  all_goals reduce_mod_char

set_option maxRecDepth 4000 in
set_option maxHeartbeats 8000000 in
theorem action3_eq (x : Core) : action3 x = action1 (action2 x) := by
  apply Core.ext <;> simp only [action3, action2, action1] <;> ring_nf
  all_goals reduce_mod_char

def action (i : Fin 4) (x : Core) : Core :=
  if i = 0 then x else if i = 1 then action1 x else if i = 2 then action2 x else action3 x

theorem action_eq (i : Fin 4) (x : Core) : action i x = (representative 2 ^ i.val) x := by
  fin_cases i <;> simp [action, action3_eq, action2_eq, action1_eq, pow_succ, MulAut.mul_apply]

def cmul {ε : Bool} (x y : Model 2 ε) : Model 2 ε :=
  ⟨x.core * action x.idx y.core * CyclicFourCentralExtension.mark ε ^ ((x.idx.val + y.idx.val) / 4),
    ⟨(x.idx.val + y.idx.val) % 4, Nat.mod_lt _ (by decide)⟩⟩

theorem cmul_eq {ε : Bool} (x y : Model 2 ε) : cmul x y = x * y := by
  unfold cmul
  rw [action_eq]
  rfl

end ReeTwo.FixingModel.Two
