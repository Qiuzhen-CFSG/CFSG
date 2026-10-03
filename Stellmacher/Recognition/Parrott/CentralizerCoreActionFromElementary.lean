module

public import Stellmacher.Recognition.Parrott.CentralizerActionData
public import Stellmacher.Recognition.Parrott.CentralizerCoreActionRigidity
public import Stellmacher.Recognition.Parrott.DerivedCentralizer
/-!
# Recovering the core action from the elementary action

The exact equations (20)–(22) determine the four images on J/J′ without
changing any coordinate. For the first image, aʳ and d have the same
conjugation action on the elementary derived generators. Their quotient
therefore centralizes J′, which is self-centralizing, so aʳ lies in dJ′.
The intrinsic triple-commutator rigidity gives the b- and c-images, and
involutivity gives the d-image.

This reduces the remaining coordinate normalization to errors in the actual
elementary derived subgroup. In addition, the discrepancy ryrx⁻¹rx fixes all
five derived generators, hence belongs to that same self-centralizing subgroup.
No choice between the alternatives preceding (23), and no equation (23) or
(24), is assumed.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.680–681, equations (20)–(23).
-/

open Subgroup
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
private def rc (k : G) : G →* G where
  toFun g := k⁻¹ * g * k
  map_one' := by simp
  map_mul' g h := by simp [mul_assoc]
private theorem rc_fixed {k g : G} (hc : Commute k g) : rc k g = g := by
  change k⁻¹ * g * k = g
  rw [mul_assoc, ← hc.eq, inv_mul_cancel_left]
private theorem rc_pc {k g z : G} (hp : Tits.parrottCommutator k g = z)
    (hz : z ^ 2 = 1) : rc k g = g * z := by
  have hh := (Tits.parrottCommutator_eq_iff _ _ _).mp hp
  have hzz : z * z = 1 := by simpa only [pow_two] using hz
  change k⁻¹ * g * k = g * z
  have hh' := congrArg (fun q => k⁻¹ * q * z) hh
  simpa only [mul_assoc, inv_mul_cancel_left, hzz, mul_one] using hh'.symm
private theorem comm_cancel {k g h : G} (hg : Commute k g)
    (hgh : Commute k (g * h)) : Commute k h := by
  simpa only [inv_mul_cancel_left] using hg.inv_right.mul_right hgh

/-- The exact elementary action forces aʳ to belong to the original coset dJ′. -/
public theorem ParrottCentralizerInvolutionData.a_image_mod_derived [Finite G]
    (f : ParrottCentralizerInvolutionData n) (h : ParrottCentralizerHypotheses z) :
    f.d⁻¹ * (f.r⁻¹ * f.a * f.r) ∈ ParrottCore.Derived z := by
  let R := rc f.r
  let ar := R f.a
  have Rz : R z = z := rc_fixed f.comm_zr.symm
  have Rt : R n.t = f.w * f.u * n.v * z := f.eq20_tr
  have Rv : R n.v = f.u * n.v := f.eq21_vr
  have Ru : R f.u = f.u := f.eq22_ur
  have Rw : R f.w = n.v * n.t * z := f.eq22_wr
  have hz : Commute ar z := by simpa only [Rz] using f.comm_az.map R
  have hu : Commute ar f.u := by simpa only [Ru] using f.comm_au.map R
  have hv : Commute ar n.v := by
    apply comm_cancel hu
    simpa only [Rv] using f.comm_av.map R
  have hw : Commute ar f.w := by
    have hh : Commute ar (f.w * (f.u * n.v * z)) := by
      simpa only [Rt, mul_assoc] using f.comm_at.map R
    have hh' := hh.mul_right ((hu.mul_right hv).mul_right hz).inv_right
    simpa only [mul_inv_cancel_right] using hh'
  have ht : rc ar n.t = n.t * z := by
    have hp : Tits.parrottCommutator ar (n.v * n.t * z) = z := by
      have hh := congrArg R f.eq02_aw
      simpa only [ParrottCore.map_parrottCommutator, Rw, Rz] using hh
    have hh := rc_pc hp f.z_sq
    rw [map_mul, map_mul, rc_fixed hv, rc_fixed hz] at hh
    have hzz : z * z = 1 := by simpa only [pow_two] using f.z_sq
    have hiz : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
    calc
      rc ar n.t = n.v⁻¹ * (n.v * rc ar n.t * z) * z⁻¹ := by group
      _ = n.v⁻¹ * (n.v * n.t * z * z) * z⁻¹ := by rw [hh]
      _ = n.t * z := by rw [mul_assoc (n.v*n.t), hzz, mul_one, hiz]; group
  have hd : f.d⁻¹ = f.d :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using f.d_sq)
  have hdt : rc f.d n.t = n.t * z := rc_pc f.eq03_dt f.z_sq
  have commute_of_actions (g : G) (heq : rc ar (rc f.d g) = g) :
      Commute g (f.d⁻¹ * ar) := by
    change g * (f.d⁻¹ * ar) = (f.d⁻¹ * ar) * g
    have hh := congrArg (fun q => f.d * ar * q) heq
    simp only [rc, MonoidHom.coe_mk, OneHom.coe_mk] at hh
    rw [hd]
    have hdd : f.d * f.d = 1 := by simpa only [pow_two] using f.d_sq
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, hdd, one_mul] using hh
  have hs : f.d⁻¹ * ar ∈ centralizer (ParrottCore.Derived z : Set G) := by
    have hle : ParrottCore.Derived z ≤ centralizer ({f.d⁻¹ * ar} : Set G) := by
      rw [ParrottCore.Derived, ← f.derived_basis]
      apply (closure_le _).mpr
      intro g hg
      apply mem_centralizer_singleton_iff.mpr
      apply commute_of_actions
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl
      · rw [rc_fixed f.comm_zd.symm, rc_fixed hz]
      · rw [hdt, map_mul, ht, rc_fixed hz, mul_assoc, ← pow_two, f.z_sq, mul_one]
      · rw [rc_fixed f.toParrottSylowGeneratorData.core_commute_d_v, rc_fixed hv]
      · rw [rc_fixed ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq08_du), rc_fixed hu]
      · rw [rc_fixed ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq07_dw), rc_fixed hw]
    intro g hg
    exact mem_centralizer_singleton_iff.mp (hle hg)
  have hCE : centralizer (ParrottCore.Derived z : Set G) = ParrottCore.Derived z :=
    parrott_derived_centralizer z h
  rw [hCE] at hs
  exact hs

/-- All four core images, modulo the actual derived subgroup, follow from
(20)–(22). The supplied involution and entire Sylow frame are unchanged. -/
public theorem ParrottCentralizerInvolutionData.core_images_mod_derived [Finite G]
    (f : ParrottCentralizerInvolutionData n) (h : ParrottCentralizerHypotheses z) :
    f.d⁻¹ * (f.r⁻¹ * f.a * f.r) ∈ ParrottCore.Derived z ∧
      (f.d * f.c * f.b)⁻¹ * (f.r⁻¹ * f.b * f.r) ∈ ParrottCore.Derived z ∧
      (f.c * f.d * f.a)⁻¹ * (f.r⁻¹ * f.c * f.r) ∈ ParrottCore.Derived z ∧
      f.a⁻¹ * (f.r⁻¹ * f.d * f.r) ∈ ParrottCore.Derived z := by
  have hr : f.r ∈ centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.mpr f.comm_zr.symm.eq
  have ha := f.a_image_mod_derived h
  obtain ⟨hb, hc⟩ := f.toParrottSylowGeneratorData.core_orientation_remaining_images
    h f.r hr f.eq20_r ha
  exact ⟨ha, hb, hc,
    f.toParrottSylowGeneratorData.core_orientation_d_image_of_a_image f.r hr f.eq20_r ha⟩

private theorem rc_mul (k l j : G) : rc (k * l) j = rc l (rc k j) := by
  simp [rc, mul_assoc]

/-- Before any normalization of the core action, the discrepancy already
belongs to the actual derived subgroup. -/
public theorem ParrottCentralizerInvolutionData.discrepancy_mem_derived [Finite G]
    (f : ParrottCentralizerInvolutionData n) (h : ParrottCentralizerHypotheses z) :
    f.r * f.y * f.r * (f.x⁻¹ * f.r * f.x) ∈ ParrottCore.Derived z := by
  have Xz := rc_fixed f.comm_zx.symm
  have Xt := rc_fixed ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq01_xt)
  have Xv := rc_pc f.eq01_xv f.t_sq
  have Xu := rc_pc f.eq01_xu f.v_sq
  have Xw := rc_pc f.eq01_xw f.u_sq
  have Zz := rc_fixed (Commute.refl z)
  have Zt := rc_fixed f.comm_zt
  have Zv := rc_fixed f.comm_zv
  have Zu := rc_fixed f.comm_zu
  have Zw := rc_fixed f.comm_zw
  have Rz := rc_fixed f.comm_zr.symm
  have Rt : rc f.r n.t = _ := f.eq20_tr
  have Rv : rc f.r n.v = _ := f.eq21_vr
  have Ru : rc f.r f.u = _ := f.eq22_ur
  have Rw : rc f.r f.w = _ := f.eq22_wr
  have y_word : f.y = f.x * f.x * z := by
    apply mul_right_cancel (b := z)
    simp only [mul_assoc, ← pow_two, f.z_sq, mul_one, f.eq04]
  have xi_word : f.x⁻¹ = f.x * f.y * z := by
    apply inv_eq_of_mul_eq_one_right
    calc
      f.x * (f.x * f.y * z) = (f.x * f.x) * f.y * z := by group
      _ = (f.y * z) * f.y * z := by rw [← pow_two, f.eq04]
      _ = 1 := by simp only [mul_assoc, f.comm_zy.eq, ← pow_two, f.y_sq,
        mul_one, f.z_sq]
  have zz : z * z = 1 := by simpa only [pow_two] using f.z_sq
  have tt : n.t * n.t = 1 := by simpa only [pow_two] using f.t_sq
  have vv : n.v * n.v = 1 := by simpa only [pow_two] using f.v_sq
  have uu : f.u * f.u = 1 := by simpa only [pow_two] using f.u_sq
  have ww : f.w * f.w = 1 := by simpa only [pow_two] using f.w_sq
  have tail {a b c : G} (hh : a * b = c) (d : G) : a * (b * d) = c * d := by
    rw [← mul_assoc, hh]
  let q := f.r * f.y * f.r * (f.x⁻¹ * f.r * f.x)
  have fixes : rc q z = z ∧ rc q n.t = n.t ∧ rc q n.v = n.v ∧
      rc q f.u = f.u ∧ rc q f.w = f.w := by
    dsimp only [q]
    rw [xi_word, y_word]
    simp only [rc_mul, map_mul, Xz, Xt, Xv, Xu, Xw, Zz, Zt, Zv, Zu, Zw,
      Rz, Rt, Rv, Ru, Rw]
    simp only [mul_assoc, one_mul, mul_one, zz, tt, vv, uu,
      tail tt, tail vv, tail uu, tail ww,
      f.comm_zt.eq, tail f.comm_zt.eq, f.comm_zv.eq, tail f.comm_zv.eq,
      f.comm_zu.eq, tail f.comm_zu.eq, tail f.comm_zw.eq,
      f.comm_tv.eq, tail f.comm_tv.eq, tail f.comm_tu.eq,
      tail f.comm_tw.eq, f.comm_vu.eq, tail f.comm_vu.eq,
      tail f.comm_vw.eq, f.comm_uw.eq, tail f.comm_uw.eq,
      and_self]
  have hle : ParrottCore.Derived z ≤ centralizer ({q} : Set G) := by
    rw [ParrottCore.Derived, ← f.derived_basis]
    apply (closure_le _).mpr
    intro j hj
    have hjfix : rc q j = j := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl
      · exact fixes.1
      · exact fixes.2.1
      · exact fixes.2.2.1
      · exact fixes.2.2.2.1
      · exact fixes.2.2.2.2
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (fun k => q * k) hjfix
    simpa only [rc, MonoidHom.coe_mk, OneHom.coe_mk, ← mul_assoc,
      mul_inv_cancel, one_mul] using hh
  have hq : q ∈ centralizer (ParrottCore.Derived z : Set G) := by
    intro j hj
    exact mem_centralizer_singleton_iff.mp (hle hj)
  have hCE : centralizer (ParrottCore.Derived z : Set G) = ParrottCore.Derived z :=
    parrott_derived_centralizer z h
  exact hCE ▸ hq

end Stellmacher.Recognition
