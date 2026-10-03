module

public import Stellmacher.Recognition.Parrott.NormalizerGeneratorSeedActions

/-!
# The cubic relation for Parrott's normalizer seed

For the selected x-image, conjugation P by sd sends x to catz and its third
iterate sends x to xt. The previously established membership (sd)³ ∈ F then
identifies the cube: on the elementary abelian group F, the norm
`g ↦ g * P(g) * P²(g)` is multiplicative and takes values in {1, vz}, as can
be checked on the five generators. Since (sd)³ is P-fixed, it equals its norm.
The x-action excludes the identity, giving (sd)³ = vz. Finally P fixes vz,
so (sdvz)³ = 1.

All calculations use the supplied seed and centralizer frame. In particular,
the x-image is an explicit premise, independent of its branch-exclusion proof.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.682, the derivation of equation (26).
-/

open Subgroup Tits
open scoped IsMulCommutative
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
    (c*w*u)*(a*u)*w*(t*z)*z = c*a*t*z ∧
    (x*a*b*c*u*v)*(y*b*w)*(a*u)*u*v*(t*z) = x*y*c*a*w*v*t*z ∧
    (y*b*w)*(a*u)*v*z = y*b*a*w*u*v ∧
    (x*y*c*a*w*v*t*z)*u*z*(t*z) = x*y*c*a*w*u*v*z ∧
    (c*a*t*z)*(w*u*v*z)*(x*y*c*a*w*v*t*z)*u*(y*b*a*w*u*v)*(a*u)*(v*t)*(t*z) = x*t := by
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

private def conj (q : G) : G →* G where
  toFun g := q⁻¹ * g * q
  map_one' := by group
  map_mul' := by intro g h; group

private theorem conj_mul_apply (q r g : G) : conj (q*r) g = conj r (conj q g) := by
  dsimp [conj]
  group

private theorem conj_right {g q h : G} (hh : parrottCommutator g q = h) :
    conj q g = g*h := by
  have hh := (parrottCommutator_eq_iff _ _ _).mp hh
  change q⁻¹*g*q = g*h
  calc
    _ = q⁻¹*(g*q) := by group
    _ = g*h := by rw [hh]; group

private theorem conj_left {g q h : G} (hh : parrottCommutator q g = h)
    (hs : h^2=1) : conj q g = g*h := by
  have hh := (parrottCommutator_eq_iff _ _ _).mp hh
  change q⁻¹*g*q = g*h
  calc
    _ = q⁻¹*(q*g)*h⁻¹ := by rw [hh]; group
    _ = g*h := by rw [sq_inv hs]; group

private theorem conj_commute {q g : G} (hh : Commute q g) : conj q g = g := by
  change q⁻¹*g*q = g
  rw [mul_assoc, hh.symm.eq]
  group

namespace ParrottNormalizerSeedData
variable {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerSeedData f)

set_option linter.unusedSimpArgs false in
private theorem sd_actions
    (hx : k.s⁻¹*f.x*k.s = f.c*f.a*f.w*n.t*z) :
    let P := conj (k.s*f.d)
    P z = n.t*z ∧ P n.t = z ∧ P n.v = n.v*n.t ∧
    P f.a = f.u ∧ P f.u = f.a*f.u ∧
    P f.x = f.c*f.a*n.t*z ∧
    P f.c = f.x*f.y*f.c*f.a*f.w*n.v*n.t*z ∧
    P f.w = f.y*f.b*f.a*f.w*f.u*n.v ∧
    P f.y = f.w*f.u*n.v*z := by
  have zs : conj k.s z = n.t := k.z_conj
  have ts : conj k.s n.t = z := k.t_conj
  have vs : conj k.s n.v = n.v*n.t*z := k.v_conj
  have aas : conj k.s f.a = f.u := k.a_conj_eq
  have us : conj k.s f.u = f.a := k.u_conj
  have xs : conj k.s f.x = f.c*f.a*f.w*n.t*z := hx
  have cs : conj k.s f.c = f.x*f.y*f.a*f.u*n.v*n.t := k.c_conj_of_x_conj hx
  have ws : conj k.s f.w = f.y*f.a*n.v*z := k.w_conj
  have ys : conj k.s f.y = f.w*f.u*n.v*z := k.y_conj
  have zd : conj f.d z = z := conj_commute f.comm_zd.symm
  have td : conj f.d n.t = n.t*z := conj_left f.eq03_dt f.z_sq
  have vd : conj f.d n.v = n.v := conj_commute (d_v f.toParrottSylowGeneratorData)
  have ud : conj f.d f.u = f.u := conj_commute ((parrottCommutator_eq_one_iff _ _).mp f.eq08_du)
  have ad : conj f.d f.a = f.a*f.u := conj_right f.eq11_ad
  have wd : conj f.d f.w = f.w := conj_commute ((parrottCommutator_eq_one_iff _ _).mp f.eq07_dw)
  have cd : conj f.d f.c = f.c*f.w*f.u := by
    simpa only [mul_assoc] using conj_right f.eq14_cd
  have xd : conj f.d f.x = f.x*f.a*f.b*f.c*f.u*n.v := by
    simpa only [mul_assoc] using conj_right f.eq19_xd
  have yd : conj f.d f.y = f.y*f.b*f.w := by
    simpa only [mul_assoc] using conj_right f.eq17_yd
  dsimp only
  simp only [conj_mul_apply, zs, ts, vs, aas, us, xs, cs, ws, ys,
    map_mul, zd, td, vd, ud, ad, wd, cd, xd, yd]
  have zz : z*z=1 := by simpa only [pow_two] using f.z_sq
  have words := word_calculations f.toParrottSylowGeneratorData
  exact ⟨True.intro, True.intro, by simp only [mul_assoc, zz, mul_one], True.intro, True.intro,
    words.1, words.2.1, words.2.2.1, True.intro⟩

private theorem x_conj_cube
    (hx : k.s⁻¹*f.x*k.s = f.c*f.a*f.w*n.t*z) :
    conj ((k.s*f.d)^3) f.x = f.x*n.t := by
  let P := conj (k.s*f.d)
  obtain ⟨hz, ht, hv, ha, hu, hxx, hc, hw, hy⟩ := k.sd_actions hx
  have hp2 : P (P f.x) = f.x*f.y*f.c*f.a*f.w*f.u*n.v*z := by
    change conj (k.s*f.d) (conj (k.s*f.d) f.x) = _
    rw [hxx, map_mul, map_mul, map_mul, hc, ha, ht, hz]
    exact (word_calculations f.toParrottSylowGeneratorData).2.2.2.1
  calc
    _ = P (P (P f.x)) := by
      dsimp [P, conj]
      simp only [pow_succ, pow_zero]
      group
    _ = f.x*n.t := by
      rw [hp2]
      change conj (k.s*f.d) _ = _
      simp only [map_mul, hxx, hy, hc, ha, hw, hu, hv, hz]
      exact (word_calculations f.toParrottSylowGeneratorData).2.2.2.2


set_option linter.unusedSimpArgs false in
private theorem norm_cases
    (hx : k.s⁻¹*f.x*k.s = f.c*f.a*f.w*n.t*z)
    (g : G) (hg : g ∈ e.F) :
    let P := conj (k.s*f.d)
    g*P g*P (P g) = 1 ∨ g*P g*P (P g) = n.v*z := by
  let _ := e.elementary
  let P := conj (k.s*f.d)
  change g*P g*P (P g) = 1 ∨ g*P g*P (P g) = n.v*z
  obtain ⟨hz, ht, hv, ha, hu, _⟩ := k.sd_actions hx
  change P z = _ at hz
  change P n.t = _ at ht
  change P n.v = _ at hv
  change P f.a = _ at ha
  change P f.u = _ at hu
  have gen_mem (g : G) (hg : g ∈ ({z,n.t,n.v,f.u,f.a} : Set G)) : g ∈ e.F := by
    rw [← f.elementary_basis]
    exact subset_closure hg
  have zm := gen_mem z (by simp)
  have tm := gen_mem n.t (by simp)
  have vm := gen_mem n.v (by simp)
  have um := gen_mem f.u (by simp)
  have am := gen_mem f.a (by simp)
  have pres : e.F ≤ e.F.comap P := by
    nth_rw 1 [← f.elementary_basis]
    apply (Subgroup.closure_le _).mpr
    intro g hg
    change P g ∈ e.F
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · rw [hz]; exact e.F.mul_mem tm zm
    · rw [ht]; exact zm
    · rw [hv]; exact e.F.mul_mem vm tm
    · rw [hu]; exact e.F.mul_mem am um
    · rw [ha]; exact um
  have norm_mul (g h : G) (hg : g ∈ e.F) (hh : h ∈ e.F) :
      (g*h)*P (g*h)*P (P (g*h)) = (g*P g*P (P g))*(h*P h*P (P h)) := by
    simp only [map_mul]
    exact congrArg e.F.subtype (show
      ((⟨g,hg⟩ : e.F)*⟨h,hh⟩)*(⟨P g,pres hg⟩*⟨P h,pres hh⟩)*
          (⟨P (P g),pres (pres hg)⟩*⟨P (P h),pres (pres hh)⟩) =
        (⟨g,hg⟩*⟨P g,pres hg⟩*⟨P (P g),pres (pres hg)⟩)*
          (⟨h,hh⟩*⟨P h,pres hh⟩*⟨P (P h),pres (pres hh)⟩) from by ac_rfl)
  have zz : z*z=1 := by simpa only [pow_two] using f.z_sq
  have tt : n.t*n.t=1 := by simpa only [pow_two] using f.t_sq
  have vv : n.v*n.v=1 := by simpa only [pow_two] using f.v_sq
  have aa : f.a*f.a=1 := by simpa only [pow_two] using f.a_sq
  have uu : f.u*f.u=1 := by simpa only [pow_two] using f.u_sq
  have vzsq : (n.v*z)*(n.v*z)=1 := by
    simp only [mul_assoc, tail f.comm_zv.eq, tail vv, zz, one_mul]
  rw [← f.elementary_basis] at hg
  induction hg using closure_induction with
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    all_goals simp only [map_mul, hz, ht, hv, hu, ha]
    all_goals simp only [mul_assoc, tail f.comm_zt.eq, f.comm_zt.eq,
      tail f.comm_tv.eq, f.comm_tv.eq, tail f.comm_au.symm.eq, f.comm_au.symm.eq,
      tail zz, zz, tail tt, tt, tail vv, vv, tail aa, aa, tail uu, uu,
      one_mul, mul_one, true_or, or_true]
  | one => simp only [map_one, one_mul, true_or]
  | mul g h hg hh ihg ihh =>
    rw [norm_mul g h (f.elementary_basis ▸ hg) (f.elementary_basis ▸ hh)]
    rcases ihg with hg' | hg' <;> rcases ihh with hh' | hh'
    all_goals simp only [hg', hh', one_mul, mul_one, vzsq, true_or, or_true]
  | inv g hg ih =>
    have hi : g⁻¹=g := sq_inv (elemPow_eq_one_of_isElementaryAbelian g
      (show g ∈ e.F from f.elementary_basis ▸ hg))
    simpa only [hi] using ih


/-- The selected x-image identifies the cube of sd inside F. -/
public theorem cube_sd_eq_vz_of_x_conj
    (hx : k.s⁻¹*f.x*k.s = f.c*f.a*f.w*n.t*z) :
    (k.s*f.d)^3 = n.v*z := by
  let _ := e.elementary
  let q := (k.s*f.d)^3
  have hq : q ∈ e.F := k.cube_sd_mem_elementary
  have fixed : conj (k.s*f.d) q = q := by
    dsimp [conj, q]
    simp only [pow_succ, pow_zero]
    group
  have qq : q*q=1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) q hq
  have cases := k.norm_cases hx q hq
  dsimp only at cases
  simp only [fixed, qq, one_mul] at cases
  rcases cases with h1 | h1
  · have hxc := k.x_conj_cube hx
    change conj q f.x = _ at hxc
    rw [h1] at hxc
    have hh : f.x = f.x*n.t := by simpa [conj] using hxc
    have ht : n.t=1 := mul_left_cancel (hh.symm.trans (mul_one f.x).symm)
    exact (n.t_not_mem_zpowers (ht ▸ (one_mem _))).elim
  · exact h1

/-- Equation (26), conditional only on the selected x-image of the seed. -/
public theorem cube_eq_one_of_x_conj
    (hx : k.s⁻¹*f.x*k.s = f.c*f.a*f.w*n.t*z) :
    (k.s*f.d*n.v*z)^3 = 1 := by
  obtain ⟨hz, _, hv, _⟩ := k.sd_actions hx
  have tt : n.t*n.t=1 := by simpa only [pow_two] using f.t_sq
  have zz : z*z=1 := by simpa only [pow_two] using f.z_sq
  have vv : n.v*n.v=1 := by simpa only [pow_two] using f.v_sq
  have fixed : conj (k.s*f.d) (n.v*z) = n.v*z := by
    rw [map_mul, hv, hz]
    simp only [mul_assoc, tail tt, one_mul]
  have hc : Commute (k.s*f.d) (n.v*z) := by
    show (k.s*f.d)*(n.v*z) = (n.v*z)*(k.s*f.d)
    calc
      _ = (k.s*f.d)*conj (k.s*f.d) (n.v*z) := by rw [fixed]
      _ = _ := by dsimp [conj]; group
  have vzsq : (n.v*z)*(n.v*z)=1 := by
    simp only [mul_assoc, tail f.comm_zv.eq, tail vv, zz, one_mul]
  calc
    _ = ((k.s*f.d)*(n.v*z))^3 := by rw [mul_assoc (k.s*f.d)]
    _ = (k.s*f.d)^3 * (n.v*z)^3 := hc.mul_pow 3
    _ = 1 := by
      rw [k.cube_sd_eq_vz_of_x_conj hx]
      simp only [pow_succ, pow_zero, one_mul, vzsq]

end ParrottNormalizerSeedData
end Stellmacher.Recognition
