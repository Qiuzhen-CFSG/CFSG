module

public import Stellmacher.Recognition.Parrott.NormalizerTransportData
public import Theory.GroupTheory.CyclicExtension
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators

/-!
# Removing the u-coordinate in Parrott's transported root

Suppose an involution transports t, v, y as prescribed and sends a to u or uz.
If its x-image is caw times an element of ⟨u,t,z⟩, its transporter can be
replaced so that the discrepancy belongs to ⟨t,z⟩. The supplied centralizer
frame and all transport fields are retained literally.

Write the discrepancy as uⁱd with d in ⟨t,z⟩. When i = 1, transporting
[x,w] = u excludes aˢ = u. Involutivity then determines the images of u, w
and c, and transporting [x,c] = abuv gives bˢ = bauv. Consequently s
inverts ab, so s(ab) is another involution. Conjugation by ab fixes t, v
and wuvz, while sending caw to cawuz and u to uz. Thus s(ab) removes the
u-factor and leaves d unchanged. No root census or orbit assumption is used.

The scalar collection follows the established technique in
`NormalizerGeneratorSeedActions`, using only the supplied Sylow equations.
Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.682, the paragraph selecting the image of x.
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
private theorem correction_words :
    y * (a * (v*t*z) * t)⁻¹ = y*a*v*z ∧
    y * ((a*t) * (v*t*z) * t)⁻¹ = y*a*v*t*z ∧
    parrottCommutator (c*a*w*(u)) (y*a*v*z) = a*t ∧
    (u*z) * parrottCommutator (c*a*w*(u)) (x*((u*z)*(y*a*v*t*z)*((a*t)))⁻¹) * (v*t*z) * (a*t) = b*a*u*v ∧
    parrottCommutator (c*a*w*(u*z)) (y*a*v*z) = a*t ∧
    (u*z) * parrottCommutator (c*a*w*(u*z)) (x*((u*z)*(y*a*v*t*z)*((a*t)*t))⁻¹) * (v*t*z) * (a*t) = b*a*u*v ∧
    parrottCommutator (c*a*w*(u*t)) (y*a*v*z) = a*t ∧
    (u*z) * parrottCommutator (c*a*w*(u*t)) (x*((u*z)*(y*a*v*t*z)*((a*t)*z))⁻¹) * (v*t*z) * (a*t) = b*a*u*v ∧
    parrottCommutator (c*a*w*(u*t*z)) (y*a*v*z) = a*t ∧
    (u*z) * parrottCommutator (c*a*w*(u*t*z)) (x*((u*z)*(y*a*v*t*z)*((a*t)*z*t))⁻¹) * (v*t*z) * (a*t) = b*a*u*v ∧
    (a*b)⁻¹*(c*a*w)*(a*b) = c*a*w*u*z ∧
    (a*b)⁻¹*u*(a*b) = u*z ∧
    (a*b)⁻¹*(w*u*v*z)*(a*b) = w*u*v*z ∧
    (u*z)*(b*a*u*v) = (a*b)⁻¹ := by
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

variable {f : ParrottCentralizerGeneratorData n}

private def S (k : ParrottNormalizerTransportData f) : G →* G where
  toFun g := k.s⁻¹ * g * k.s
  map_one' := by group
  map_mul' g h := by group

private theorem SS (k : ParrottNormalizerTransportData f) (g : G) :
    S k (S k g) = g := by
  change k.s⁻¹ * (k.s⁻¹ * g * k.s) * k.s = g
  rw [sq_inv k.sq]
  have hs : k.s * k.s = 1 := by simpa only [pow_two] using k.sq
  calc
    _ = (k.s * k.s) * g * (k.s * k.s) := by group
    _ = g := by rw [hs]; simp

private theorem w_image (k : ParrottNormalizerTransportData f)
    (ha : S k f.a = f.u) : S k f.w = f.y*f.a*n.v*z := by
  have zs : S k z = n.t := k.z_conj
  have vs : S k n.v = n.v*n.t*z := k.v_conj
  have ys : S k f.y = f.w*f.u*n.v*z := k.y_conj
  have us : S k f.u = f.a := by rw [← ha, SS]
  have hh := congrArg (S k) ys
  rw [SS, map_mul, map_mul, map_mul, us, vs, zs] at hh
  calc
    _ = f.y * (f.a*(n.v*n.t*z)*n.t)⁻¹ := by rw [hh]; group
    _ = _ := (correction_words f.toParrottSylowGeneratorData).1

private theorem u_w_images (k : ParrottNormalizerTransportData f)
    (ha : S k f.a = f.u*z) :
    S k f.u = f.a*n.t ∧ S k f.w = f.y*f.a*n.v*n.t*z := by
  have zs : S k z = n.t := k.z_conj
  have vs : S k n.v = n.v*n.t*z := k.v_conj
  have ys : S k f.y = f.w*f.u*n.v*z := k.y_conj
  have tt : n.t*n.t = 1 := by simpa only [pow_two] using f.t_sq
  have hh := congrArg (S k) ha
  rw [SS, map_mul, zs] at hh
  have us : S k f.u = f.a*n.t := by rw [hh, mul_assoc, tt, mul_one]
  refine ⟨us, ?_⟩
  have hh := congrArg (S k) ys
  rw [SS, map_mul, map_mul, map_mul, us, vs, zs] at hh
  calc
    _ = f.y * ((f.a*n.t)*(n.v*n.t*z)*n.t)⁻¹ := by rw [hh]; group
    _ = _ := (correction_words f.toParrottSylowGeneratorData).2.1

private theorem ab_inverted (k : ParrottNormalizerTransportData f)
    (ha : S k f.a = f.u ∨ S k f.a = f.u*z)
    (d : G) (hd : d ∈ closure ({n.t,z} : Set G))
    (hx : S k f.x = f.c*f.a*f.w*(f.u*d)) :
    S k (f.a*f.b) = (f.a*f.b)⁻¹ := by
  have dc := (mem_closure_pair_iff n.t z
    (by simpa only [pow_two] using f.t_sq)
    (by simpa only [pow_two] using f.z_sq) f.comm_zt.symm d).mp hd
  rcases correction_words f.toParrottSylowGeneratorData with
    ⟨W0,W1,C00,B00,C01,B01,C10,B10,C11,B11,QX,QU,QY,QI⟩
  have ht1 : n.t ≠ 1 := fun hh => n.t_not_mem_zpowers (hh ▸ one_mem _)
  rcases ha with ha | ha
  · have us : S k f.u = f.a := by rw [← ha, SS]
    have ws := w_image k ha
    have hh := congrArg (S k) f.eq01_xw
    simp only [parrottCommutator, map_mul, map_inv] at hh
    change parrottCommutator (S k f.x) (S k f.w) = S k f.u at hh
    rw [hx, ws, us] at hh
    have he : f.a*n.t = f.a := by
      rcases dc with rfl | rfl | rfl | rfl
      · exact C00.symm.trans (by simpa only [mul_one] using hh)
      · simpa only [mul_assoc] using C10.symm.trans hh
      · simpa only [mul_assoc] using C01.symm.trans hh
      · exact C11.symm.trans (by simpa only [mul_assoc] using hh)
    exact (ht1 (mul_left_cancel (he.trans (mul_one f.a).symm))).elim
  · obtain ⟨us, ws⟩ := u_w_images k ha
    have ts : S k n.t = z := k.t_conj
    have zs : S k z = n.t := k.z_conj
    have vs : S k n.v = n.v*n.t*z := k.v_conj
    have hh := congrArg (S k) hx
    rw [SS, map_mul, map_mul, map_mul, map_mul, ha, ws, us] at hh
    have cs : S k f.c = f.x*((f.u*z)*(f.y*f.a*n.v*n.t*z)*((f.a*n.t)*S k d))⁻¹ := by
      rw [hh]; group
    have bb : f.b = f.a * parrottCommutator f.x f.c * n.v * f.u := by
      rw [f.eq19_xc]
      have aa : f.a*f.a=1 := by simpa only [pow_two] using f.a_sq
      have uu : f.u*f.u=1 := by simpa only [pow_two] using f.u_sq
      have vv : n.v*n.v=1 := by simpa only [pow_two] using f.v_sq
      simp only [mul_assoc, tail aa, tail vv, uu, mul_one, one_mul]
    have bs : S k f.b = f.b*f.a*f.u*n.v := by
      conv_lhs => rw [bb]
      rw [map_mul, map_mul, map_mul, ha, vs, us]
      have hm : S k (parrottCommutator f.x f.c) =
          parrottCommutator (S k f.x) (S k f.c) := by
        simp only [parrottCommutator, map_mul, map_inv]
      rw [hm, hx, cs]
      rcases dc with rfl | rfl | rfl | rfl
      · simpa only [map_one, mul_one] using B00
      · simpa only [ts, mul_assoc] using B10
      · simpa only [zs, mul_assoc] using B01
      · simpa only [map_mul, ts, zs, mul_assoc] using B11
    rw [map_mul, ha, bs]
    exact QI

private theorem conj_fixed {p q : G} (h : Commute p q) : p⁻¹*q*p = q := by
  rw [mul_assoc, ← h.eq]; group

private theorem ab_commutes_t : Commute (f.a*f.b) n.t :=
  f.comm_at.mul_left f.comm_bt

private theorem ab_commutes_v : Commute (f.a*f.b) n.v := by
  have hb : Commute f.b n.v := by
    rw [← f.eq03_b]
    exact Commute.self_pow f.b 2
  exact f.comm_av.mul_left hb

private theorem ab_commutes_z : Commute (f.a*f.b) z :=
  f.comm_az.mul_left f.comm_zb.symm

private def twistAB (k : ParrottNormalizerTransportData f)
    (hi : S k (f.a*f.b) = (f.a*f.b)⁻¹) : ParrottNormalizerTransportData f where
  s := k.s*(f.a*f.b)
  mem_normalizer := by
    have ha := f.local_mem_sylow.2.2.2.2.2.1
    have hb := f.local_mem_sylow.2.2.2.2.2.2.1
    exact mul_mem k.mem_normalizer (e.sylow_le_normalizer (mul_mem ha hb))
  sq := by
    have hs : k.s*k.s=1 := by simpa only [pow_two] using k.sq
    calc
      _ = (k.s*k.s) * S k (f.a*f.b) * (f.a*f.b) := by dsimp [S]; simp only [pow_two]; group
      _ = 1 := by rw [hs, hi]; group
  t_conj := by
    calc
      _ = (f.a*f.b)⁻¹*(k.s⁻¹*n.t*k.s)*(f.a*f.b) := by group
      _ = z := by rw [k.t_conj]; exact conj_fixed ab_commutes_z
  v_conj := by
    calc
      _ = (f.a*f.b)⁻¹*(k.s⁻¹*n.v*k.s)*(f.a*f.b) := by group
      _ = n.v*n.t*z := by
        rw [k.v_conj]
        exact conj_fixed ((ab_commutes_v.mul_right ab_commutes_t).mul_right ab_commutes_z)
  y_conj := by
    calc
      _ = (f.a*f.b)⁻¹*(k.s⁻¹*f.y*k.s)*(f.a*f.b) := by group
      _ = f.w*f.u*n.v*z := by
        rw [k.y_conj]
        exact (correction_words f.toParrottSylowGeneratorData).2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem twistAB_x (k : ParrottNormalizerTransportData f)
    (hi : S k (f.a*f.b) = (f.a*f.b)⁻¹)
    (d : G) (hd : d ∈ closure ({n.t,z} : Set G))
    (hx : S k f.x = f.c*f.a*f.w*(f.u*d)) :
    (twistAB k hi).s⁻¹*f.x*(twistAB k hi).s = f.c*f.a*f.w*d := by
  let C : G →* G := {
    toFun g := (f.a*f.b)⁻¹*g*(f.a*f.b)
    map_one' := by group
    map_mul' g h := by group }
  have ct : C n.t = n.t := conj_fixed ab_commutes_t
  have cz : C z = z := conj_fixed ab_commutes_z
  have cd : C d = d := by
    rcases (mem_closure_pair_iff n.t z
      (by simpa only [pow_two] using f.t_sq)
      (by simpa only [pow_two] using f.z_sq) f.comm_zt.symm d).mp hd with
      rfl | rfl | rfl | rfl
    · exact map_one C
    · exact ct
    · exact cz
    · rw [map_mul, ct, cz]
  have words := correction_words f.toParrottSylowGeneratorData
  have cx : C (f.c*f.a*f.w) = f.c*f.a*f.w*f.u*z := words.2.2.2.2.2.2.2.2.2.2.1
  have cu : C f.u = f.u*z := words.2.2.2.2.2.2.2.2.2.2.2.1
  change (k.s*(f.a*f.b))⁻¹*f.x*(k.s*(f.a*f.b)) = _
  calc
    _ = C (S k f.x) := by dsimp [C,S]; group
    _ = (f.c*f.a*f.w*f.u*z)*((f.u*z)*d) := by
      rw [hx, map_mul C (f.c*f.a*f.w), cx, map_mul C f.u, cu, cd]
    _ = f.c*f.a*f.w*d := by
      have hu : (f.u*z)^2=1 := by
        rw [f.comm_zu.symm.mul_pow, f.u_sq, f.z_sq, one_mul]
      calc
        _ = (f.c*f.a*f.w)*((f.u*z)^2)*d := by simp only [pow_two, mul_assoc]
        _ = _ := by rw [hu]; group

/-- Remove the u-coordinate by the involution s(ab), retaining the literal
supplied frame and all transport equations. -/
public theorem ParrottNormalizerTransportData.exists_corrected_of_u_discrepancy
    [Finite G] (k : ParrottNormalizerTransportData f)
    (ha : k.s⁻¹*f.a*k.s = f.u ∨ k.s⁻¹*f.a*k.s = f.u*z)
    (hx : (f.c*f.a*f.w)⁻¹*(k.s⁻¹*f.x*k.s) ∈ closure ({f.u,n.t,z} : Set G)) :
    ∃ k0 : ParrottNormalizerTransportData f,
      (f.c*f.a*f.w)⁻¹*(k0.s⁻¹*f.x*k0.s) ∈ closure ({n.t,z} : Set G) := by
  have huN : ∀ b ∈ ({n.t,z} : Set G),
      f.u*b*f.u⁻¹ ∈ closure ({n.t,z} : Set G) := by
    intro b hb
    have hc : Commute f.u b := by
      rcases hb with rfl | hb
      · exact f.comm_tu.symm
      · have he : b=z := Set.mem_singleton_iff.mp hb
        rw [he]; exact f.comm_zu.symm
    rw [hc.eq, mul_inv_cancel_right]
    exact subset_closure hb
  obtain ⟨d, hd, i, hdi⟩ := Theory.GroupTheory.exists_mul_pow_of_mem_closure_insert
    ({n.t,z} : Set G) f.u 2 (by decide) f.u_sq huN hx
  fin_cases i
  · simp only [pow_zero, mul_one] at hdi
    exact ⟨k, hdi ▸ hd⟩
  · simp only [pow_one] at hdi
    have du : Commute d f.u := by
      rcases (mem_closure_pair_iff n.t z
        (by simpa only [pow_two] using f.t_sq)
        (by simpa only [pow_two] using f.z_sq) f.comm_zt.symm d).mp hd with
        rfl | rfl | rfl | rfl
      · exact Commute.one_left _
      · exact f.comm_tu
      · exact f.comm_zu
      · exact f.comm_tu.mul_left f.comm_zu
    have xx : S k f.x = f.c*f.a*f.w*(f.u*d) := by
      change k.s⁻¹*f.x*k.s = _
      rw [du.eq] at hdi
      exact inv_mul_eq_iff_eq_mul.mp hdi.symm
    have hi := ab_inverted k ha d hd xx
    refine ⟨twistAB k hi, ?_⟩
    rw [twistAB_x k hi d hd xx, inv_mul_cancel_left]
    exact hd

end Stellmacher.Recognition
