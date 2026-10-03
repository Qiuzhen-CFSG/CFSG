module

public import Theory.SpecificGroups.ReeTwo.RootAction

/-!
# Packed arithmetic for the core action census

Encode the ten binary coordinates as an integer. Every packed operation is
proved to agree with the original core operation. The table for the order-five
action is checked on the presentation generators and extended to all elements
by the normal form. This forces intermediate calculations to integers during
kernel-checked finite certificates.

Source: the verified Shinoda (1975), (2.3), core coordinates and action in
`Core` and `RootAction`. The encoding follows `SylowPackedArithmetic`.
-/

@[expose] public section
namespace ReeTwo.Core.CensusPacked

def code (x : Core) : Nat :=
  x.b0.val + 2*x.b1.val + 4*x.b2.val + 8*x.b3.val + 16*x.b4.val +
  32*x.b5.val + 64*x.b6.val + 128*x.b7.val + 256*x.b8.val + 512*x.b9.val

def decode (n : Nat) : Core :=
  ⟨n, (n/2 : Nat), (n/4 : Nat), (n/8 : Nat), (n/16 : Nat), (n/32 : Nat), (n/64 : Nat), (n/128 : Nat), (n/256 : Nat), (n/512 : Nat)⟩

theorem decode_code (x : Core) : decode (code x) = x := by
  have h0 := ZMod.val_lt x.b0
  have h1 := ZMod.val_lt x.b1
  have h2 := ZMod.val_lt x.b2
  have h3 := ZMod.val_lt x.b3
  have h4 := ZMod.val_lt x.b4
  have h5 := ZMod.val_lt x.b5
  have h6 := ZMod.val_lt x.b6
  have h7 := ZMod.val_lt x.b7
  have h8 := ZMod.val_lt x.b8
  have h9 := ZMod.val_lt x.b9
  apply Core.ext <;> apply ZMod.val_injective <;>
    simp only [decode, code, ZMod.val_natCast] <;> omega

theorem code_lt (x : Core) : code x < 1024 := by
  have h0 := ZMod.val_lt x.b0
  have h1 := ZMod.val_lt x.b1
  have h2 := ZMod.val_lt x.b2
  have h3 := ZMod.val_lt x.b3
  have h4 := ZMod.val_lt x.b4
  have h5 := ZMod.val_lt x.b5
  have h6 := ZMod.val_lt x.b6
  have h7 := ZMod.val_lt x.b7
  have h8 := ZMod.val_lt x.b8
  have h9 := ZMod.val_lt x.b9
  dsimp [code]
  omega

theorem code_injective : Function.Injective code := by
  intro x y h
  rw [← decode_code x, h, decode_code]

def pmul (x y : Nat) : Nat :=
  match x, y with
  | 0, 0 => code (decode 0 * decode 0)
  | 0, y + 1 => code (decode 0 * decode (y + 1))
  | x + 1, 0 => code (decode (x + 1) * decode 0)
  | x + 1, y + 1 => code (decode (x + 1) * decode (y + 1))

theorem pmul_eq (x y : Nat) : pmul x y = code (decode x * decode y) := by
  cases x <;> cases y <;> rfl
theorem pmul_code (x y : Core) : pmul (code x) (code y) = code (x*y) := by
  simp only [pmul_eq, decode_code]
def ppow (x : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => pmul (ppow x n) x
theorem ppow_code (x : Core) (n : Nat) : ppow (code x) n = code (x^n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ppow, ih, pmul_code, pow_succ]

def actRaw (r : CoreRoot → Nat) (n : Nat) : Nat :=
  let v := coords (decode n)
  pmul (pmul (pmul (pmul (pmul (pmul (pmul (pmul (pmul
    (ppow (r 0) (v 0).val) (ppow (r 1) (v 1).val)) (ppow (r 2) (v 2).val))
    (ppow (r 3) (v 3).val)) (ppow (r 4) (v 4).val)) (ppow (r 5) (v 5).val))
    (ppow (r 6) (v 6).val)) (ppow (r 7) (v 7).val)) (ppow (r 8) (v 8).val))
    (ppow (r 9) (v 9).val)

def act (r : CoreRoot → Nat) (n : Nat) : Nat :=
  match n with
  | 0 => actRaw r 0
  | n + 1 => actRaw r (n + 1)

theorem act_eq (r : CoreRoot → Nat) (n : Nat) : act r n = actRaw r n := by
  cases n <;> rfl

theorem act_code (r : CoreRoot → Core) (x : Core) :
    act (fun i => code (r i)) (code x) = code (normalWord r (coords x)) := by
  simp only [act_eq, actRaw, decode_code, ppow_code, pmul_code, normalWord]


def peval (r : CoreRoot → Nat) : List CoreRoot → Nat
  | [] => 0
  | i :: w => pmul (r i) (peval r w)
theorem peval_code (r : CoreRoot → Core) (w : List CoreRoot) :
    peval (fun i => code (r i)) w = code (rootWord r w) := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [peval, ih, pmul_code, rootWord_cons]

def pinv (n : Nat) : Nat := pmul (pmul n n) n
theorem pinv_code (x : Core) : pinv (code x) = code x⁻¹ := by
  simp only [pinv, pmul_code]
  rfl

def pcomm (x y : Nat) : Nat := pmul (pmul (pmul (pinv x) (pinv y)) x) y
theorem pcomm_code (x y : Core) : pcomm (code x) (code y) = code (rightComm x y) := by
  simp only [pcomm, pinv_code, pmul_code, rightComm]



def cRoots : CoreRoot → Nat := ![16, 8, 4, 786, 765, 256, 128, 320, 928, 512]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem cRoots_eq : ∀ i, cRoots i = code (c (root i)) := by
  decide +kernel

def cAct : Nat → Nat := act cRoots

theorem cAct_code (x : Core) : cAct (code x) = code (c x) := by
  have hr : cRoots = fun i => code (c (root i)) := funext cRoots_eq
  rw [cAct, hr, act_code]
  have h := map_normalWord c.toMonoidHom root (coords x)
  simp only [normalWord_root, ofCoords_coords] at h
  exact congrArg code h.symm

theorem cAct_iterate_code (n : Nat) (x : Core) :
    (cAct^[n]) (code x) = code ((c ^ n) x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, cAct_code, ih, pow_succ]
    rfl
end ReeTwo.Core.CensusPacked
