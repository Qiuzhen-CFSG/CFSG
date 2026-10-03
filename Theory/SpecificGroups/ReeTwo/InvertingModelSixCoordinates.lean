module

public import Theory.SpecificGroups.ReeTwo.InvertingModelFirstCoreBasic

/-!
# Collected action for the sixth inverting model

The three polynomial actions are checked against the root presentation and
composition. They supply efficient, kernel-checked arithmetic for both choices
of the actor's fourth power.

Source: Shinoda (1975), (2.3), through `Core` and the sixth row of
`InvertingActionRepresentatives`.
-/

@[expose] public section
namespace ReeTwo.InvertingModel.Six
open Core.InvertingActionCensus

def action1 (x : Core) : Core where
  b0 := x.b0 + x.b1 + x.b3 + x.b4
  b1 := x.b1 + x.b3
  b2 := x.b2 + x.b3 + x.b4
  b3 := x.b3 + x.b4
  b4 := x.b4
  b5 := x.b1 + x.b1 * x.b3 + x.b2 * x.b3 + x.b4 + x.b2 * x.b4 + x.b5 + x.b6 + x.b7 + x.b8
  b6 := x.b0 + x.b2 * x.b3 + x.b3 * x.b4 + x.b6 + x.b7
  b7 := x.b3 + x.b4 + x.b3 * x.b4 + x.b7 + x.b8
  b8 := x.b3 + x.b4 + x.b3 * x.b4 + x.b8
  b9 := x.b2 + x.b3 + x.b0 * x.b3 + x.b4 + x.b0 * x.b4 + x.b1 * x.b4 + x.b1 * x.b3 * x.b4 + x.b7 + x.b8 + x.b9

def action2 (x : Core) : Core where
  b0 := x.b0 + x.b3 + x.b4
  b1 := x.b1 + x.b4
  b2 := x.b2 + x.b4
  b3 := x.b3
  b4 := x.b4
  b5 := x.b0 + x.b3 + x.b2 * x.b3 + x.b1 * x.b4 + x.b2 * x.b4 + x.b3 * x.b4 + x.b5 + x.b7 + x.b8
  b6 := x.b1 + x.b3 + x.b2 * x.b4 + x.b3 * x.b4 + x.b6 + x.b8
  b7 := x.b3 + x.b4 + x.b3 * x.b4 + x.b7
  b8 := x.b8
  b9 := x.b1 * x.b3 + x.b0 * x.b4 + x.b1 * x.b4 + x.b8 + x.b9

def action3 (x : Core) : Core where
  b0 := x.b0 + x.b1 + x.b4
  b1 := x.b1 + x.b3 + x.b4
  b2 := x.b2 + x.b3
  b3 := x.b3 + x.b4
  b4 := x.b4
  b5 := x.b0 + x.b3 + x.b1 * x.b3 + x.b1 * x.b4 + x.b2 * x.b4 + x.b3 * x.b4 + x.b5 + x.b6 + x.b8
  b6 := x.b0 + x.b1 + x.b3 + x.b2 * x.b3 + x.b2 * x.b4 + x.b6 + x.b7 + x.b8
  b7 := x.b7 + x.b8
  b8 := x.b3 + x.b4 + x.b3 * x.b4 + x.b8
  b9 := x.b2 + x.b3 + x.b0 * x.b3 + x.b1 * x.b3 + x.b4 + x.b1 * x.b3 * x.b4 + x.b7 + x.b9

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

theorem action1_eq (x : Core) : action1 x = representative 6 x := by
  have h : actionHom = (representative 6).toMonoidHom := by
    apply Core.hom_ext
    exact (by decide +kernel : ∀ i : CoreRoot,
      actionHom (Core.root i) = representative 6 (Core.root i))
  exact DFunLike.congr_fun h x

set_option maxHeartbeats 8000000 in
theorem action2_eq (x : Core) : action2 x = action1 (action1 x) := by
  apply Core.ext <;> simp only [action2, action1, action1] <;> ring_nf
  all_goals reduce_mod_char
  all_goals simp only [show ∀ z : ZMod 2, z ^ 2 = z from by decide]
  all_goals ring_nf
  all_goals reduce_mod_char

set_option maxHeartbeats 8000000 in
theorem action3_eq (x : Core) : action3 x = action1 (action2 x) := by
  apply Core.ext <;> simp only [action3, action2, action1] <;> ring_nf
  all_goals reduce_mod_char
  all_goals simp only [show ∀ z : ZMod 2, z ^ 2 = z from by decide]
  all_goals ring_nf
  all_goals reduce_mod_char

def action (i : Fin 4) (x : Core) : Core :=
  if i = 0 then x else if i = 1 then action1 x else if i = 2 then action2 x else action3 x

theorem action_eq (i : Fin 4) (x : Core) : action i x = (representative 6 ^ i.val) x := by
  fin_cases i <;> simp [action, action3_eq, action2_eq, action1_eq, pow_succ, MulAut.mul_apply]

def cmul {ε : Bool} (x y : Model 6 ε) : Model 6 ε :=
  ⟨x.core * action x.idx y.core * CyclicFourCentralExtension.mark ε ^ ((x.idx.val + y.idx.val) / 4),
    ⟨(x.idx.val + y.idx.val) % 4, Nat.mod_lt _ (by decide)⟩⟩

theorem cmul_eq {ε : Bool} (x y : Model 6 ε) : cmul x y = x * y := by
  unfold cmul
  rw [action_eq]
  rfl

open Core.CensusPacked

def code {ε : Bool} (x : Model 6 ε) : Nat := Core.CensusPacked.code x.core + 1024 * x.idx.val

def decode (ε : Bool) (n : Nat) : Model 6 ε :=
  ⟨Core.CensusPacked.decode (n % 1024), ⟨n / 1024 % 4, Nat.mod_lt _ (by decide)⟩⟩

theorem code_injective {ε : Bool} : Function.Injective (code (ε := ε)) := by
  intro x y h
  have hx := Core.CensusPacked.code_lt x.core
  have hy := Core.CensusPacked.code_lt y.core
  unfold code at h
  apply CyclicFourCentralExtension.Model.ext
  · apply Core.CensusPacked.code_injective
    omega
  · apply Fin.ext
    omega

theorem code_lt {ε : Bool} (x : Model 6 ε) : code x < 4096 := by
  have hx := Core.CensusPacked.code_lt x.core
  have hi := x.idx.isLt
  unfold code
  omega

theorem decode_code {ε : Bool} (x : Model 6 ε) : decode ε (code x) = x := by
  have hx := Core.CensusPacked.code_lt x.core
  have ex : code x % 1024 = Core.CensusPacked.code x.core := by unfold code; omega
  have ix : code x / 1024 = x.idx.val := by unfold code; omega
  apply CyclicFourCentralExtension.Model.ext
  · change Core.CensusPacked.decode (code x % 1024) = x.core
    rw [ex, Core.CensusPacked.decode_code]
  · apply Fin.ext
    simp [decode, ix]

def paction (i : Fin 4) (n : Nat) : Nat :=
  match n with
  | 0 => Core.CensusPacked.code (action i (Core.CensusPacked.decode 0))
  | n + 1 => Core.CensusPacked.code (action i (Core.CensusPacked.decode (n + 1)))

theorem paction_eq (i : Fin 4) (n : Nat) :
    paction i n = Core.CensusPacked.code (action i (Core.CensusPacked.decode n)) := by
  cases n <;> rfl

def pmul (ε : Bool) (x y : Nat) : Nat :=
  Core.CensusPacked.pmul
    (Core.CensusPacked.pmul (x % 1024) (paction ⟨x / 1024 % 4, Nat.mod_lt _ (by decide)⟩ (y % 1024)))
    (if ε && (x / 1024 + y / 1024 ≥ 4) then 512 else 0) +
    1024 * ((x / 1024 + y / 1024) % 4)

theorem pmul_code (ε : Bool) (x y : Model 6 ε) : pmul ε (code x) (code y) = code (x * y) := by
  have hx := Core.CensusPacked.code_lt x.core
  have hy := Core.CensusPacked.code_lt y.core
  have ex : code x % 1024 = Core.CensusPacked.code x.core := by unfold code; omega
  have ey : code y % 1024 = Core.CensusPacked.code y.core := by unfold code; omega
  have ix : code x / 1024 = x.idx.val := by unfold code; omega
  have iy : code y / 1024 = y.idx.val := by unfold code; omega
  have fi : (⟨code x / 1024 % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = x.idx := by
    apply Fin.ext
    simp [ix]
  unfold pmul
  rw [ex, ey, fi, paction_eq, Core.CensusPacked.decode_code, ix, iy,
    Core.CensusPacked.pmul_code]
  have hm : (if ε && (x.idx.val + y.idx.val ≥ 4) then 512 else 0) =
      Core.CensusPacked.code (CyclicFourCentralExtension.mark ε ^ ((x.idx.val + y.idx.val) / 4)) := by
    exact (by decide +kernel : ∀ (ε : Bool) (i j : Fin 4),
      (if ε && (i.val + j.val ≥ 4) then 512 else 0) =
        Core.CensusPacked.code (CyclicFourCentralExtension.mark ε ^ ((i.val + j.val) / 4))) ε x.idx y.idx
  rw [hm, Core.CensusPacked.pmul_code, action_eq]
  rfl

end ReeTwo.InvertingModel.Six
