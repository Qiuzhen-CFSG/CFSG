module

public import Stellmacher.Recognition.Parrott.NormalizerGeneratorSeed

/-!
# Actions determined by Parrott's reduced normalizer seed

Involutivity exchanges z and t. Applying it to the a and y images, and then
transporting [x,w]=u, removes the possible z-factor in the a-image. The y-image
then determines w, the x-image determines c, and [x,c]=abuv determines b.
These are finite collection calculations in the supplied Sylow coordinates.

Conjugation by sd has order dividing three on the five generators of F.
Consequently (sd)³ lies in C_G(F)=F. This supplies a reduction for identifying
the cube once the remaining x-image has been selected. All results preserve
the supplied seed involution and centralizer frame.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.682, the calculation preceding (25) and the derivation of (26).
The collection technique follows `Tits.RecognitionLocalSylowRelations`.
-/

open Subgroup Tits
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
section Scalar
variable (f : ParrottSylowGeneratorData n)
local notation "t" => n.t
local notation "v" => n.v
local notation "u" => f.u
local notation "w" => f.w
local notation "a" => f.a
local notation "b" => f.b
local notation "c" => f.c
local notation "d" => f.d
local notation "x" => f.x
local notation "y" => f.y

private theorem tail {p q o : G} (hp : p * q = o) (k : G) :
    p * (q * k) = o * k := by rw [← mul_assoc, hp]

private theorem sq_inv {p : G} (hp : p ^ 2 = 1) : p⁻¹ = p :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hp)

private theorem reverse {p q o : G} (hp : p * q = q * p * o) :
    q * p = p * q * o⁻¹ := by rw [hp]; group

set_option linter.unusedSimpArgs false in
private theorem y_actions :
    y * v = v * y ∧ y * u = u * y * t ∧ y * w = w * y * v := by
  have vx := reverse ((parrottCommutator_eq_iff x v t).mp f.eq01_xv)
  have ux := reverse ((parrottCommutator_eq_iff x u v).mp f.eq01_xu)
  have wx := reverse ((parrottCommutator_eq_iff x w u).mp f.eq01_xw)
  have tx := ((parrottCommutator_eq_one_iff x t).mp f.eq01_xt).symm.eq
  simp only [sq_inv f.t_sq, sq_inv f.v_sq, sq_inv f.u_sq] at vx ux wx
  have yy : y = x * x * z := by
    apply mul_right_cancel («b» := z)
    simp only [mul_assoc, ← pow_two, f.z_sq, mul_one, f.eq04]
  have vv : v*v=1 := by simpa only [pow_two] using f.v_sq
  have tt : t*t=1 := by simpa only [pow_two] using f.t_sq
  have uu : u*u=1 := by simpa only [pow_two] using f.u_sq
  rw [yy]
  constructor
  · simp only [mul_assoc, tail vx, vx, tail tx, tx, tail f.comm_zv.eq,
      f.comm_zv.eq, tail tt, tt, one_mul, mul_one]
  constructor
  · simp only [mul_assoc, tail ux, ux, tail vx, vx, tail f.comm_zu.eq,
      tail f.comm_vu.eq, tail f.comm_zv.eq, tail f.comm_zt.eq,
      tail f.comm_tv.eq, f.comm_zu.eq, f.comm_zv.eq, f.comm_zt.eq,
      f.comm_tv.eq, tail vv, vv, tail tt, tt, one_mul, mul_one]
  · simp only [mul_assoc, tail wx, wx, tail ux, ux, tail f.comm_zw.eq,
      tail f.comm_uw.eq, tail f.comm_zv.eq, tail f.comm_zt.eq,
      tail f.comm_tv.eq, tail f.comm_vu.eq, f.comm_zw.eq, f.comm_zv.eq,
      f.comm_uw.eq, f.comm_vu.eq, tail vv, vv, tail uu, uu, one_mul, mul_one]

private theorem d_v : d * v = v * d := by
  have dd : d*d=1 := by simpa only [pow_two] using f.d_sq
  calc
    d * v = v⁻¹ * d := by
      rw [← f.eq03_db]
      simp only [parrottCommutator, mul_inv_rev, inv_inv, sq_inv f.d_sq]
      group
      simp only [mul_assoc, dd, one_mul, mul_one]
    _ = v * d := by rw [sq_inv f.v_sq]

set_option linter.unusedSimpArgs false in
private theorem word_calculations :
    y * (a * (v*t*z) * t)⁻¹ = y*a*v*z ∧
    y * ((a*t) * (v*t*z) * t)⁻¹ = y*a*v*t*z ∧
    parrottCommutator (c*a*w) (y*a*v*t*z) = a ∧
    parrottCommutator (c*a*w*t*z) (y*a*v*t*z) = a ∧
    x * (u * (y*a*v*z))⁻¹ = x*y*a*u*v*z ∧
    x * (u * (y*a*v*z) * z * t)⁻¹ = x*y*a*u*v*t ∧
    u * parrottCommutator (c*a*w) (x*y*a*u*v*z) * (v*t*z) * a = b*a*u*v*z ∧
    u * parrottCommutator (c*a*w*t*z) (x*y*a*u*v*t) * (v*t*z) * a = b*a*u*v*z := by
  have yv := (y_actions f).1
  have yu := (y_actions f).2.1
  have yw := (y_actions f).2.2
  have dv := d_v f
  have y_eq : y = x ^ 2 * z := by
    apply mul_right_cancel («b» := z)
    simp only [mul_assoc, ← pow_two, f.z_sq, mul_one, f.eq04]
  have yx : y*x=x*y := by
    rw [y_eq]
    exact (((Commute.refl x).pow_left 2).mul_left f.comm_zx).eq
  have yt : y*t=t*y := by
    rw [y_eq]
    exact ((((parrottCommutator_eq_one_iff x t).mp f.eq01_xt).pow_left 2).mul_left f.comm_zt).eq
  have ya := (parrottCommutator_eq_one_iff y a).mp f.eq06_ya
  have byc := (parrottCommutator_eq_one_iff b y).mp f.eq18_by
  have ax := (parrottCommutator_eq_one_iff a x).mp f.eq16_ax
  have tx := ((parrottCommutator_eq_one_iff x t).mp f.eq01_xt).symm
  have bw := (parrottCommutator_eq_one_iff b w).mp f.eq02_bw
  have dw := (parrottCommutator_eq_one_iff d w).mp f.eq07_dw
  have du := (parrottCommutator_eq_one_iff d u).mp f.eq08_du
  have cu := (parrottCommutator_eq_one_iff c u).mp f.eq09_cu
  have cw := (parrottCommutator_eq_one_iff c w).mp f.eq09_cw
  have ct := (parrottCommutator_eq_one_iff c t).mp f.eq10_ct
  have bv : Commute b v := by
    rw [← f.eq03_b]
    exact Commute.self_pow b 2
  have vx := reverse ((parrottCommutator_eq_iff x v t).mp f.eq01_xv)
  have ux := reverse ((parrottCommutator_eq_iff x u v).mp f.eq01_xu)
  have wx := reverse ((parrottCommutator_eq_iff x w u).mp f.eq01_xw)
  have cx := reverse ((parrottCommutator_eq_iff x c (a*b*u*v)).mp f.eq19_xc)
  have bx := (parrottCommutator_eq_iff b x a).mp f.eq18_bx
  have aw := (parrottCommutator_eq_iff a w z).mp f.eq02_aw
  have wa := reverse aw
  simp only [sq_inv f.z_sq] at wa
  have ub := reverse ((parrottCommutator_eq_iff b u z).mp f.eq02_bu)
  have bd := reverse ((parrottCommutator_eq_iff d b v).mp f.eq03_db)
  have td := reverse ((parrottCommutator_eq_iff d t z).mp f.eq03_dt)
  have ab := (parrottCommutator_eq_iff a b t).mp f.eq05_ab
  have vc := reverse ((parrottCommutator_eq_iff c v z).mp f.eq10_cv)
  have ad := (parrottCommutator_eq_iff a d u).mp f.eq11_ad
  have ac := (parrottCommutator_eq_iff a c (v*t)).mp f.eq12_ac
  have cd := (parrottCommutator_eq_iff c d (w*u)).mp f.eq14_cd
  have bc := (parrottCommutator_eq_iff b c (u*v)).mp f.eq15_bc
  have cy := reverse ((parrottCommutator_eq_iff y c (a*t*z)).mp f.eq19_yc)
  have dy := reverse ((parrottCommutator_eq_iff y d (b*w)).mp f.eq17_yd)
  have uy := reverse yu
  have wy := reverse yw
  have zz : z*z=1 := by simpa only [pow_two] using f.z_sq
  have tt : t*t=1 := by simpa only [pow_two] using f.t_sq
  have vv : v*v=1 := by simpa only [pow_two] using f.v_sq
  have uu : u*u=1 := by simpa only [pow_two] using f.u_sq
  have ww : w*w=1 := by simpa only [pow_two] using f.w_sq
  have aa : a*a=1 := by simpa only [pow_two] using f.a_sq
  have dd : d*d=1 := by simpa only [pow_two] using f.d_sq
  have yy : y*y=1 := by simpa only [pow_two] using f.y_sq
  have bb : b*b=v := by simpa only [pow_two] using f.eq03_b
  have cc : c*c=w*u := by simpa only [pow_two] using f.eq13
  have xx : x*x=y*z := by simpa only [pow_two] using f.eq04
  have binv : b⁻¹ = b*v := by
    apply inv_eq_of_mul_eq_one_right
    simp only [← mul_assoc, bb, vv]
  have xinv : x⁻¹ = x*y*z := by
    apply inv_eq_of_mul_eq_one_right
    simp only [mul_assoc, tail xx, tail f.comm_zy.eq, tail yy, zz, one_mul]
  simp only [mul_inv_rev, sq_inv f.z_sq, sq_inv f.t_sq, sq_inv f.v_sq,
    sq_inv f.u_sq, sq_inv f.w_sq, sq_inv f.a_sq, binv] at vx ux wx cx ub bd td vc cy dy uy wy
  have cinv : c⁻¹ = c*w*u := by
    apply inv_eq_of_mul_eq_one_right
    simp only [mul_assoc, tail cc, tail f.comm_uw.eq, tail ww, uu, one_mul]
  simp only [parrottCommutator, mul_inv_rev, sq_inv f.z_sq, sq_inv f.t_sq,
    sq_inv f.v_sq, sq_inv f.u_sq, sq_inv f.w_sq, sq_inv f.a_sq, sq_inv f.y_sq,
    xinv, cinv, binv, mul_assoc]
  simp only [mul_assoc, one_mul, mul_one, and_true, true_and,
    tail (vx), vx,
    tail (ux), ux,
    tail (wx), wx,
    tail (cx), cx,
    tail (bx), bx,
    tail (ax.eq), ax.eq,
    tail (tx.eq), tx.eq,
    tail (f.comm_zx.eq), f.comm_zx.eq,
    tail (yx), yx,
    tail (byc.eq), byc.eq,
    tail (cy), cy,
    tail (dy), dy,
    tail (ya.symm.eq), ya.symm.eq,
    tail (uy), uy,
    tail (wy), wy,
    tail (yv.symm), yv.symm,
    tail (yt.symm), yt.symm,
    tail (f.comm_zy.eq), f.comm_zy.eq,
    tail (cd), cd,
    tail (bd), bd,
    tail (ad), ad,
    tail (dw.symm.eq), dw.symm.eq,
    tail (du.symm.eq), du.symm.eq,
    tail (dv.symm), dv.symm,
    tail (td), td,
    tail (f.comm_zd.eq), f.comm_zd.eq,
    tail (bc), bc,
    tail (ac), ac,
    tail (cw.symm.eq), cw.symm.eq,
    tail (cu.symm.eq), cu.symm.eq,
    tail (vc), vc,
    tail (ct.symm.eq), ct.symm.eq,
    tail (f.comm_zc.eq), f.comm_zc.eq,
    tail (ab), ab,
    tail (bw.symm.eq), bw.symm.eq,
    tail (ub), ub,
    tail (bv.symm.eq), bv.symm.eq,
    tail (f.comm_bt.symm.eq), f.comm_bt.symm.eq,
    tail (f.comm_zb.eq), f.comm_zb.eq,
    tail wa, wa,
    tail (f.comm_au.symm.eq), f.comm_au.symm.eq,
    tail (f.comm_av.symm.eq), f.comm_av.symm.eq,
    tail (f.comm_at.symm.eq), f.comm_at.symm.eq,
    tail (f.comm_az.symm.eq), f.comm_az.symm.eq,
    tail (f.comm_uw.eq), f.comm_uw.eq,
    tail (f.comm_vw.eq), f.comm_vw.eq,
    tail (f.comm_tw.eq), f.comm_tw.eq,
    tail (f.comm_zw.eq), f.comm_zw.eq,
    tail (f.comm_vu.eq), f.comm_vu.eq,
    tail (f.comm_tu.eq), f.comm_tu.eq,
    tail (f.comm_zu.eq), f.comm_zu.eq,
    tail (f.comm_tv.eq), f.comm_tv.eq,
    tail (f.comm_zv.eq), f.comm_zv.eq,
    tail (f.comm_zt.eq), f.comm_zt.eq,
    tail (zz), zz,
    tail (tt), tt,
    tail (vv), vv,
    tail (uu), uu,
    tail (ww), ww,
    tail (aa), aa,
    tail (dd), dd,
    tail (yy), yy,
    tail (bb), bb,
    tail (cc), cc,
    tail (xx), xx]

end Scalar

namespace ParrottNormalizerSeedData
variable {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerSeedData f)

private theorem conjugation_involutive (g : G) :
    k.s⁻¹ * (k.s⁻¹ * g * k.s) * k.s = g := by
  have hs : k.s * k.s = 1 := by simpa only [pow_two] using k.sq
  rw [sq_inv k.sq]
  calc
    _ = (k.s * k.s) * g * (k.s * k.s) := by group
    _ = g := by rw [hs]; simp

/-- The seed involution exchanges z with t. -/
public theorem z_conj : k.s⁻¹ * z * k.s = n.t := by
  exact (congrArg (fun g => k.s⁻¹ * g * k.s) k.t_conj.symm).trans
    (k.conjugation_involutive n.t)

/-- The action on a has no central z-twist. -/
public theorem a_conj_eq : k.s⁻¹ * f.a * k.s = f.u := by
  let S : G →* G := {
    toFun := fun g => k.s⁻¹ * g * k.s
    map_one' := by group
    map_mul' := by intro g h; group }
  have SS (g : G) : S (S g) = g := k.conjugation_involutive g
  have zs : S z = n.t := k.z_conj
  have vs : S n.v = n.v * n.t * z := k.v_conj
  have ys : S f.y = f.w * f.u * n.v * z := k.y_conj
  rcases k.a_conj with ha | ha
  · exact ha
  change S f.a = f.u * z at ha
  have tt : n.t * n.t = 1 := by simpa only [pow_two] using f.t_sq
  have hh := congrArg S ha
  rw [SS, map_mul, zs] at hh
  have us : S f.u = f.a * n.t := by rw [hh, mul_assoc, tt, mul_one]
  have hh := congrArg S ys
  rw [SS, map_mul, map_mul, map_mul, us, vs, zs] at hh
  have ws : S f.w = f.y * f.a * n.v * n.t * z := by
    calc
      _ = f.y * ((f.a * n.t) * (n.v * n.t * z) * n.t)⁻¹ := by rw [hh]; group
      _ = _ := (word_calculations f.toParrottSylowGeneratorData).2.1
  have hxu : parrottCommutator (S f.x) (S f.w) = S f.u := by
    simpa only [parrottCommutator, map_mul, map_inv] using congrArg S f.eq01_xw
  rw [ws, us] at hxu
  have heq : f.a = f.a * n.t := by
    rcases k.x_conj with hx | hx
    · change S f.x = f.c * f.a * f.w at hx
      rw [hx, (word_calculations f.toParrottSylowGeneratorData).2.2.1] at hxu
      exact hxu
    · change S f.x = f.c * f.a * f.w * n.t * z at hx
      rw [hx, (word_calculations f.toParrottSylowGeneratorData).2.2.2.1] at hxu
      exact hxu
  have ht : n.t = 1 := mul_left_cancel (heq.symm.trans (mul_one f.a).symm)
  exact (n.t_not_mem_zpowers (ht ▸ (one_mem _))).elim

/-- The exchanged a-coordinate determines the action on u. -/
public theorem u_conj : k.s⁻¹ * f.u * k.s = f.a := by
  rw [← k.a_conj_eq]
  exact k.conjugation_involutive f.a

/-- Equation (25) for w already follows from the reduced seed. -/
public theorem w_conj : k.s⁻¹ * f.w * k.s = f.y * f.a * n.v * z := by
  let S : G →* G := {
    toFun := fun g => k.s⁻¹ * g * k.s
    map_one' := by group
    map_mul' := by intro g h; group }
  have SS (g : G) : S (S g) = g := k.conjugation_involutive g
  have zs : S z = n.t := k.z_conj
  have vs : S n.v = n.v * n.t * z := k.v_conj
  have us : S f.u = f.a := k.u_conj
  have ys : S f.y = f.w * f.u * n.v * z := k.y_conj
  have hh := congrArg S ys
  rw [SS, map_mul, map_mul, map_mul, us, vs, zs] at hh
  change S f.w = _
  calc
    _ = f.y * (f.a * (n.v * n.t * z) * n.t)⁻¹ := by rw [hh]; group
    _ = _ := (word_calculations f.toParrottSylowGeneratorData).1

/-- Involutivity determines the c-image from either remaining x-image. -/
public theorem c_conj_cases :
    (k.s⁻¹ * f.x * k.s = f.c*f.a*f.w ∧
      k.s⁻¹ * f.c * k.s = f.x*f.y*f.a*f.u*n.v*z) ∨
    (k.s⁻¹ * f.x * k.s = f.c*f.a*f.w*n.t*z ∧
      k.s⁻¹ * f.c * k.s = f.x*f.y*f.a*f.u*n.v*n.t) := by
  let S : G →* G := {
    toFun := fun g => k.s⁻¹ * g * k.s
    map_one' := by group
    map_mul' := by intro g h; group }
  have SS (g : G) : S (S g) = g := k.conjugation_involutive g
  have zs : S z = n.t := k.z_conj
  have ts : S n.t = z := k.t_conj
  have aas : S f.a = f.u := k.a_conj_eq
  have ws : S f.w = f.y*f.a*n.v*z := k.w_conj
  rcases k.x_conj with hx | hx
  · refine Or.inl ⟨hx, ?_⟩
    change S f.x = f.c*f.a*f.w at hx
    have hh := congrArg S hx
    rw [SS, map_mul, map_mul, aas, ws] at hh
    change S f.c = _
    calc
      _ = f.x * (f.u * (f.y*f.a*n.v*z))⁻¹ := by rw [hh]; group
      _ = _ := (word_calculations f.toParrottSylowGeneratorData).2.2.2.2.1
  · refine Or.inr ⟨hx, ?_⟩
    change S f.x = f.c*f.a*f.w*n.t*z at hx
    have hh := congrArg S hx
    rw [SS, map_mul, map_mul, map_mul, map_mul, aas, ws, ts, zs] at hh
    change S f.c = _
    calc
      _ = f.x * (f.u * (f.y*f.a*n.v*z) * z * n.t)⁻¹ := by rw [hh]; group
      _ = _ := (word_calculations f.toParrottSylowGeneratorData).2.2.2.2.2.1

/-- Equation (25) for b is independent of the remaining x-image choice. -/
public theorem b_conj : k.s⁻¹ * f.b * k.s = f.b*f.a*f.u*n.v*z := by
  let S : G →* G := {
    toFun := fun g => k.s⁻¹ * g * k.s
    map_one' := by group
    map_mul' := by intro g h; group }
  have aas : S f.a = f.u := k.a_conj_eq
  have us : S f.u = f.a := k.u_conj
  have vs : S n.v = n.v*n.t*z := k.v_conj
  have aa : f.a*f.a = 1 := by simpa only [pow_two] using f.a_sq
  have uu : f.u*f.u = 1 := by simpa only [pow_two] using f.u_sq
  have vv : n.v*n.v = 1 := by simpa only [pow_two] using f.v_sq
  have bb : f.b = f.a * parrottCommutator f.x f.c * n.v * f.u := by
    rw [f.eq19_xc]
    simp only [mul_assoc, tail aa, tail vv, uu, mul_one, one_mul]
  have hh := congrArg S bb
  simp only [map_mul, aas, us, vs] at hh
  have mc : S (parrottCommutator f.x f.c) = parrottCommutator (S f.x) (S f.c) := by
    simp only [parrottCommutator, map_mul, map_inv]
  rw [mc] at hh
  change S f.b = _
  rw [hh]
  rcases k.c_conj_cases with ⟨hx,hc⟩ | ⟨hx,hc⟩
  · change S f.x = _ at hx
    change S f.c = _ at hc
    rw [hx, hc]
    exact (word_calculations f.toParrottSylowGeneratorData).2.2.2.2.2.2.1
  · change S f.x = _ at hx
    change S f.c = _ at hc
    rw [hx, hc]
    exact (word_calculations f.toParrottSylowGeneratorData).2.2.2.2.2.2.2

set_option linter.unusedSimpArgs false in
/-- The cube of sd centralizes F and therefore lies in F. This uses the actual
self-centralization of F, but neither the x-branch nor a cubic relation. -/
public theorem cube_sd_mem_elementary : (k.s * f.d) ^ 3 ∈ e.F := by
  let S : G →* G := {
    toFun := fun g => k.s⁻¹ * g * k.s
    map_one' := by group
    map_mul' := by intro g h; group }
  let D : G →* G := {
    toFun := fun g => f.d⁻¹ * g * f.d
    map_one' := by group
    map_mul' := by intro g h; group }
  let P : G →* G := D.comp S
  have zs : S z = n.t := k.z_conj
  have ts : S n.t = z := k.t_conj
  have vs : S n.v = n.v*n.t*z := k.v_conj
  have aas : S f.a = f.u := k.a_conj_eq
  have us : S f.u = f.a := k.u_conj
  have zd : D z = z := by
    change f.d⁻¹*z*f.d = z
    rw [mul_assoc, f.comm_zd.eq]; group
  have ud : D f.u = f.u := by
    have hu := (parrottCommutator_eq_one_iff _ _).mp f.eq08_du
    change f.d⁻¹*f.u*f.d = f.u
    rw [mul_assoc, hu.symm.eq]; group
  have vd : D n.v = n.v := by
    change f.d⁻¹*n.v*f.d = n.v
    rw [mul_assoc, ← d_v f.toParrottSylowGeneratorData]; group
  have ad : D f.a = f.a*f.u := by
    have ha := (parrottCommutator_eq_iff _ _ _).mp f.eq11_ad
    change f.d⁻¹*f.a*f.d = f.a*f.u
    calc
      _ = f.d⁻¹*(f.a*f.d) := by group
      _ = f.a*f.u := by rw [ha]; group
  have td : D n.t = n.t*z := by
    have ht := (parrottCommutator_eq_iff _ _ _).mp f.eq03_dt
    change f.d⁻¹*n.t*f.d = n.t*z
    rw [sq_inv f.d_sq]
    calc
      _ = (n.t*f.d*z)*f.d := by rw [ht]
      _ = n.t*z := by
        have dd : f.d*f.d=1 := by simpa only [pow_two] using f.d_sq
        simp only [mul_assoc, f.comm_zd.eq, tail dd, one_mul]
  have zp : P z = n.t*z := by change D (S z) = _; rw [zs, td]
  have tp : P n.t = z := by change D (S n.t) = _; rw [ts, zd]
  have vp : P n.v = n.v*n.t := by
    change D (S n.v) = _
    rw [vs, map_mul, map_mul, vd, td, zd]
    simp only [mul_assoc, ← pow_two, f.z_sq, mul_one]
  have ap : P f.a = f.u := by change D (S f.a) = _; rw [aas, ud]
  have up : P f.u = f.a*f.u := by change D (S f.u) = _; rw [us, ad]
  have zz : z*z=1 := by simpa only [pow_two] using f.z_sq
  have tt : n.t*n.t=1 := by simpa only [pow_two] using f.t_sq
  have aa : f.a*f.a=1 := by simpa only [pow_two] using f.a_sq
  have uu : f.u*f.u=1 := by simpa only [pow_two] using f.u_sq
  have fixed : ∀ g ∈ ({z,n.t,n.v,f.u,f.a} : Set G), P (P (P g)) = g := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    all_goals simp only [map_mul, zp, tp, vp, up, ap]
    all_goals simp only [mul_assoc, tail f.comm_zt.eq, f.comm_zt.eq,
      tail f.comm_au.symm.eq, f.comm_au.symm.eq, tail zz, tail tt,
      tail aa, tail uu, zz, tt, aa, uu, one_mul, mul_one]
  rw [← e.centralizer_eq, ← f.elementary_basis, centralizer_closure]
  apply mem_centralizer_iff.mpr
  intro g hg
  have hgfix : ((k.s*f.d)^3)⁻¹*g*(k.s*f.d)^3 = g := by
    calc
      _ = P (P (P g)) := by dsimp [P, S, D]; simp only [pow_succ, pow_zero, mul_one]; group
      _ = g := fixed g hg
  calc
    g*(k.s*f.d)^3 = (k.s*f.d)^3 * (((k.s*f.d)^3)⁻¹*g*(k.s*f.d)^3) := by group
    _ = (k.s*f.d)^3*g := by rw [hgfix]

/-- The selected x-image gives precisely the c-equation of (25). -/
public theorem c_conj_of_x_conj
    (hx : k.s⁻¹*f.x*k.s = f.c*f.a*f.w*n.t*z) :
    k.s⁻¹*f.c*k.s = f.x*f.y*f.a*f.u*n.v*n.t := by
  let S : G →* G := {
    toFun := fun g => k.s⁻¹ * g * k.s
    map_one' := by group
    map_mul' := by intro g h; group }
  have SS (g : G) : S (S g) = g := k.conjugation_involutive g
  have zs : S z = n.t := k.z_conj
  have ts : S n.t = z := k.t_conj
  have aas : S f.a = f.u := k.a_conj_eq
  have ws : S f.w = f.y*f.a*n.v*z := k.w_conj
  change S f.x = f.c*f.a*f.w*n.t*z at hx
  have hh := congrArg S hx
  rw [SS, map_mul, map_mul, map_mul, map_mul, aas, ws, ts, zs] at hh
  change S f.c = _
  calc
    _ = f.x * (f.u * (f.y*f.a*n.v*z) * z * n.t)⁻¹ := by rw [hh]; group
    _ = _ := (word_calculations f.toParrottSylowGeneratorData).2.2.2.2.2.1

end ParrottNormalizerSeedData

end Stellmacher.Recognition
