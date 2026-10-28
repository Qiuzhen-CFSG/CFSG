module

public import Stellmacher.Recognition.Parrott.NormalizerRootWordSquareData
public import Stellmacher.Recognition.Parrott.NormalizerInvolutionTransportAlgebra

/-!
# Ambient evaluation of the normalizer square table

The ten binary letters are ordered x,y,c,w,b,a,u,v,t,z. Every adjacent
collection rule follows from the supplied Sylow relations (1)–(19).
A fuel-bounded collector preserves evaluation even when its fuel runs out;
therefore neither termination of unrestricted collection nor uniqueness of
normal forms is needed. Kernel reduction checks that 150 steps give the same
collected word for each proposed table entry and the corresponding doubled
word. This proves the ambient identity for every Sylow frame.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.682, the sixteen-root paragraph using equations (1)–(19).
-/

namespace Stellmacher.Recognition.ParrottNormalizerRootSquare
namespace Collection

/-- Binary letters, in collection order. -/
inductive Letter | x | y | c | w | b | a | u | v | t | z
  deriving DecidableEq
open Letter

/-- Adjacent square reductions and swaps; ordered distinct pairs need no rule. -/
def rule : Letter → Letter → Option (List Letter)
  | .x, .x => some [.y, .z]
  | .y, .x => some [.x, .y]
  | .y, .y => some []
  | .c, .x => some [.x, .c, .b, .a, .u, .z]
  | .c, .y => some [.y, .c, .a, .t, .z]
  | .c, .c => some [.w, .u]
  | .w, .x => some [.x, .w, .u]
  | .w, .y => some [.y, .w, .v]
  | .w, .c => some [.c, .w]
  | .w, .w => some []
  | .b, .x => some [.x, .b, .a]
  | .b, .y => some [.y, .b]
  | .b, .c => some [.c, .b, .u, .v]
  | .b, .w => some [.w, .b]
  | .b, .b => some [.v]
  | .a, .x => some [.x, .a]
  | .a, .y => some [.y, .a]
  | .a, .c => some [.c, .a, .v, .t]
  | .a, .w => some [.w, .a, .z]
  | .a, .b => some [.b, .a, .t]
  | .a, .a => some []
  | .u, .x => some [.x, .u, .v]
  | .u, .y => some [.y, .u, .t]
  | .u, .c => some [.c, .u]
  | .u, .w => some [.w, .u]
  | .u, .b => some [.b, .u, .z]
  | .u, .a => some [.a, .u]
  | .u, .u => some []
  | .v, .x => some [.x, .v, .t]
  | .v, .y => some [.y, .v]
  | .v, .c => some [.c, .v, .z]
  | .v, .w => some [.w, .v]
  | .v, .b => some [.b, .v]
  | .v, .a => some [.a, .v]
  | .v, .u => some [.u, .v]
  | .v, .v => some []
  | .t, .x => some [.x, .t]
  | .t, .y => some [.y, .t]
  | .t, .c => some [.c, .t]
  | .t, .w => some [.w, .t]
  | .t, .b => some [.b, .t]
  | .t, .a => some [.a, .t]
  | .t, .u => some [.u, .t]
  | .t, .v => some [.v, .t]
  | .t, .t => some []
  | .z, .x => some [.x, .z]
  | .z, .y => some [.y, .z]
  | .z, .c => some [.c, .z]
  | .z, .w => some [.w, .z]
  | .z, .b => some [.b, .z]
  | .z, .a => some [.a, .z]
  | .z, .u => some [.u, .z]
  | .z, .v => some [.v, .z]
  | .z, .t => some [.t, .z]
  | .z, .z => some []
  | _, _ => none

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
def value (f : ParrottSylowGeneratorData n) : Letter → G
  | .x => f.x
  | .y => f.y
  | .c => f.c
  | .w => f.w
  | .b => f.b
  | .a => f.a
  | .u => f.u
  | .v => n.v
  | .t => n.t
  | .z => z

def eval (f : ParrottSylowGeneratorData n) : List Letter → G
  | [] => 1
  | i :: is => value f i * eval f is

theorem eval_append (f : ParrottSylowGeneratorData n) (l r : List Letter) :
    eval f (l ++ r) = eval f l * eval f r := by
  induction l with
  | nil => simp [eval]
  | cons i l ih => simp [eval, ih, mul_assoc]

private theorem tail {a b c : G} (h : a*b=c) (d : G) : a*(b*d)=c*d := by
  rw [← mul_assoc, h]
private theorem sq_inv {g : G} (h : g^2=1) : g⁻¹=g :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h)
private theorem reverse {a b c : G} (h : a*b=b*a*c) : b*a=a*b*c⁻¹ := by
  rw [h]; group
private theorem move_of_conj {a b d : G} (h : (MulAut.conj a⁻¹) b = b*d) :
    b*a=a*b*d := by
  change a⁻¹*b*a⁻¹⁻¹=b*d at h
  have := congrArg (a * ·) h
  simpa only [inv_inv, ← mul_assoc, mul_inv_cancel, one_mul] using this

set_option maxHeartbeats 1000000 in
theorem rule_sound (f : ParrottSylowGeneratorData n) (i j : Letter) (l : List Letter)
    (h : rule i j = some l) : eval f [i,j] = eval f l := by
  have bv : Commute f.b n.v := by
    rw [← f.eq03_b]; exact Commute.self_pow _ _
  have xy : Commute f.x f.y := by
    have hy : f.y = f.x^2 * z⁻¹ := by rw [f.eq04]; group
    rw [hy]
    exact (Commute.self_pow _ _).mul_right f.comm_zx.symm.inv_right
  have ty : Commute n.t f.y := by
    have hy : f.y = f.x^2 * z⁻¹ := by rw [f.eq04]; group
    rw [hy]
    exact (((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq01_xt).symm.pow_right 2).mul_right f.comm_zt.symm.inv_right
  have vy : n.v * f.y = f.y * n.v := by
    simpa only [mul_one] using move_of_conj ((f.y_conjugation).1.trans (mul_one _).symm)
  have uy := move_of_conj f.y_conjugation.2.1
  have wy := move_of_conj f.y_conjugation.2.2
  have yx := (xy.symm).eq
  have zx := (f.comm_zx).eq
  have zy := (f.comm_zy).eq
  have zc := (f.comm_zc).eq
  have zw := (f.comm_zw).eq
  have zb := (f.comm_zb).eq
  have za := (f.comm_az.symm).eq
  have zu := (f.comm_zu).eq
  have zv := (f.comm_zv).eq
  have zt := (f.comm_zt).eq
  have ty := (ty).eq
  have tb := (f.comm_bt.symm).eq
  have ta := (f.comm_at.symm).eq
  have tu := (f.comm_tu).eq
  have tv := (f.comm_tv).eq
  have tw := (f.comm_tw).eq
  have vu := (f.comm_vu).eq
  have vw := (f.comm_vw).eq
  have uw := (f.comm_uw).eq
  have va := (f.comm_av.symm).eq
  have ua := (f.comm_au.symm).eq
  have vb := (bv.symm).eq
  have tx := (((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq01_xt).symm).eq
  have ax := (((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq16_ax)).eq
  have ay := (((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq06_ya).symm).eq
  have hby := (((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq18_by)).eq
  have bw := (((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq02_bw)).eq
  have uc := (((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq09_cu).symm).eq
  have wc := (((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq09_cw).symm).eq
  have tc := (((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq10_ct).symm).eq
  have bx := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq18_bx
  have bc := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq15_bc
  have ac := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq12_ac
  have aw := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq02_aw
  have ab := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq05_ab
  have wx := reverse ((Tits.parrottCommutator_eq_iff _ _ _).mp f.eq01_xw)
  have ux := reverse ((Tits.parrottCommutator_eq_iff _ _ _).mp f.eq01_xu)
  have vx := reverse ((Tits.parrottCommutator_eq_iff _ _ _).mp f.eq01_xv)
  have ub := reverse ((Tits.parrottCommutator_eq_iff _ _ _).mp f.eq02_bu)
  have vc := reverse ((Tits.parrottCommutator_eq_iff _ _ _).mp f.eq10_cv)
  have cy := reverse ((Tits.parrottCommutator_eq_iff _ _ _).mp f.eq19_yc)
  simp only [mul_inv_rev, sq_inv f.u_sq, sq_inv f.v_sq, sq_inv f.t_sq,
    sq_inv f.z_sq, sq_inv f.a_sq] at wx ux vx ub vc cy
  have cy' : f.c*f.y = f.y*f.c*f.a*n.t*z := by
    rw [cy]
    simp only [mul_assoc, f.comm_zt.eq, tail f.comm_az.symm.eq,
      f.comm_at.symm.eq]
  have bb : f.b*f.b=n.v := by simpa only [pow_two] using f.eq03_b
  have vv : n.v*n.v=1 := by simpa only [pow_two] using f.v_sq
  have binv : f.b⁻¹=f.b*n.v := by
    apply inv_eq_of_mul_eq_one_right
    simp only [← mul_assoc, bb, vv]
  have cx := reverse ((Tits.parrottCommutator_eq_iff _ _ _).mp f.eq19_xc)
  simp only [mul_inv_rev, sq_inv f.v_sq, sq_inv f.u_sq, sq_inv f.a_sq, binv] at cx
  have cx' : f.c*f.x=f.x*f.c*f.b*f.a*f.u*z := by
    rw [cx]
    simp only [mul_assoc, tail bv.symm.eq, tail ub,
      tail f.comm_zv.eq, tail f.comm_vu.eq, tail vv, one_mul,
      f.comm_az.symm.eq, tail f.comm_au.symm.eq]
  have xx := f.eq04
  have yy := f.y_sq
  have cc := f.eq13
  have ww := f.w_sq
  have bb := f.eq03_b
  have aa := f.a_sq
  have uu := f.u_sq
  have vv := f.v_sq
  have tt := f.t_sq
  have zz := f.z_sq
  simp only [pow_two] at xx yy cc ww bb aa uu vv tt zz
  cases i <;> cases j
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using xx
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using yx
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using yy
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using cx'
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using cy'
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using cc
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using wx
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using wy
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using wc
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using ww
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using bx
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using hby
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using bc
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using bw
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using bb
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using ax
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using ay
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using ac
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using aw
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using ab
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using aa
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using ux
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using uy
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using uc
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using uw
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using ub
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using ua
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using uu
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using vx
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using vy
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using vc
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using vw
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using vb
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using va
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using vu
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using vv
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using tx
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using ty
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using tc
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using tw
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using tb
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using ta
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using tu
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using tv
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using tt
  · simp only [rule, reduceCtorEq] at h
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using zx
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using zy
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using zc
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using zw
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using zb
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using za
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using zu
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using zv
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using zt
  · simp only [rule, Option.some.injEq] at h
    subst l
    simpa only [eval, value, mul_one, mul_assoc] using zz


/-- Perform the first available adjacent reduction. -/
def step : List Letter → Option (List Letter)
  | [] => none
  | [_] => none
  | i :: j :: rest => match rule i j with
    | some q => some (q ++ rest)
    | none => (step (j :: rest)).map (i :: ·)

theorem step_sound (f : ParrottSylowGeneratorData n) (l q : List Letter)
    (h : step l = some q) : eval f l = eval f q := by
  induction l generalizing q with
  | nil => simp [step] at h
  | cons i l ih =>
    cases l with
    | nil => simp [step] at h
    | cons j rest =>
      cases hr : rule i j with
      | some r =>
        simp only [step, hr, Option.some.injEq] at h
        subst q
        rw [eval_append, ← rule_sound f i j r hr]
        simp only [eval, mul_assoc, one_mul]
      | none =>
        simp only [step, hr] at h
        cases hs : step (j :: rest) with
        | none => simp [hs] at h
        | some r =>
          simp only [hs, Option.map_some, Option.some.injEq] at h
          subst q
          simpa only [eval] using congrArg (value f i * ·) (ih r hs)

/-- Bounded collection; soundness does not require that the bound suffices. -/
def collect : Nat → List Letter → List Letter
  | 0, l => l
  | k+1, l => match step l with
    | none => l
    | some q => collect k q

theorem collect_sound (f : ParrottSylowGeneratorData n) (k : Nat) (l : List Letter) :
    eval f (collect k l) = eval f l := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
    cases hs : step l with
    | none => simp [collect, hs]
    | some q => simpa only [collect, hs, ih] using (step_sound f l q hs).symm

def encode (p : Code) : List Letter :=
  List.replicate (p.1.val % 4) .x ++
  List.replicate (p.1.val / 4 % 4) .c ++
  List.replicate (p.1.val / 16) .b ++
  List.replicate (p.2.1.val % 2) .a ++
  List.replicate (p.2.1.val / 2 % 2) .u ++
  List.replicate (p.2.1.val / 4) .v ++
  List.replicate (p.2.2.val % 2) .t ++
  List.replicate (p.2.2.val / 2) .z

theorem eval_replicate (f : ParrottSylowGeneratorData n) (k : Nat) (i : Letter) :
    eval f (List.replicate k i) = value f i ^ k := by
  induction k with
  | zero => simp [eval]
  | succ k ih => simp [List.replicate_succ, eval, ih, pow_succ']

theorem eval_encode (f : ParrottSylowGeneratorData n) (p : Code) :
    eval f (encode p) = word f p := by
  simp only [encode, eval_append, eval_replicate, value, word, tailWord, mul_assoc]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- All 1,024 square identities, checked by kernel reduction on words. -/
theorem certificate : ∀ p : Code,
    collect 150 (encode (square p)) =
      collect 150 (encode p ++ encode p) := by
  decide +kernel

end Collection

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- The proposed square table evaluates to the actual ambient group square.
Only equations in the supplied Sylow frame are needed. -/
public theorem square_eval (f : ParrottSylowGeneratorData n) (p : Code) :
    word f (square p) = (word f p) ^ 2 := by
  have hc := congrArg (Collection.eval f) (Collection.certificate p)
  simpa only [Collection.collect_sound, Collection.eval_append,
    Collection.eval_encode, pow_two] using hc

end Stellmacher.Recognition.ParrottNormalizerRootSquare
