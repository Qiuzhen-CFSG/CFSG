module

public import Stellmacher.Recognition.Parrott.CentralizerActionParameters
public import Stellmacher.Recognition.Parrott.CentralizerCoreActionFromElementary
public import Theory.ElementaryAbelian.BinaryExpansion

/-!
# Coefficient restrictions for the centralizer action

Binary spanning in the actual elementary derived subgroup gives five Boolean
coefficients for every core-image error. Squaring the a-image removes its t
coefficient, and involutivity determines the d-image from the four remaining
coefficients, without changing the supplied frame.

Transporting [b,c] = uv determines the u exponent in the candidate c-image:
it must be α xor β. The current `HasActionParameters` interface uses α instead,
so its second parameter must be false. Moreover, any frame in the second
source a-image coset admits no parameters in that interface, even after
rechoosing all four parameters. Thus the second coset on source p.681 requires
a further exclusion or a correction to the c-image. Parameter existence is
not asserted here.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.678–681, equations (1)–(22) and the alternatives preceding (23).
-/

open Subgroup
open scoped IsMulCommutative
namespace Stellmacher.Recognition

private def act {G : Type*} [Group G] (g : G) : G →* G where
  toFun j := g⁻¹ * j * g
  map_one' := by simp
  map_mul' j k := by simp [mul_assoc]

private theorem act_comm {G : Type*} [Group G] {g j : G} (h : Commute j g) :
    act g j = j := by
  change g⁻¹ * j * g = j
  rw [mul_assoc, h.eq, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem tail {G : Type*} [Group G] {a b c : G} (h : a * b = c) (k : G) :
    a * (b * k) = c * k := by rw [← mul_assoc, h]

private theorem sqinv {G : Type*} [Group G] {a : G} (h : a ^ 2 = 1) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h)

private theorem revswap {G : Type*} [Group G] {a b c : G}
    (h : a * b = b * a * c) : b * a = a * b * c⁻¹ := by rw [h]; group

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- Every error in the actual derived subgroup has an ordered binary expansion. -/
public theorem ParrottCentralizerInvolutionData.derived_binary_expansion [Finite G]
    (f : ParrottCentralizerInvolutionData n)
    (h : ParrottCentralizerHypotheses z) {s : G} (hs : s ∈ ParrottCore.Derived z) :
    ∃ i j k l m : Bool, s = f.w ^ i.toNat * f.u ^ j.toNat *
      n.v ^ k.toNat * n.t ^ l.toNat * z ^ m.toNat := by
  let H := centralizer ({z} : Set G)
  let E := ParrottCore.Derived z
  let : IsElementaryAbelian 2 (commutator (pCore 2 H)) :=
    (parrott_centralizer_structure z h).2.2.2.2.2.1
  let : IsElementaryAbelian 2 E :=
    IsElementaryAbelian.map (H.subtype.comp (pCore 2 H).subtype)
  have mem_basis (x : G) (hx : x ∈ ({z,n.t,n.v,f.u,f.w} : Set G)) : x ∈ E := by
    change x ∈ ParrottCore.Derived z
    rw [ParrottCore.Derived, ← f.derived_basis]
    exact subset_closure hx
  let Z : E := ⟨z, mem_basis _ (by simp)⟩
  let T : E := ⟨n.t, mem_basis _ (by simp)⟩
  let V : E := ⟨n.v, mem_basis _ (by simp)⟩
  let U : E := ⟨f.u, mem_basis _ (by simp)⟩
  let W : E := ⟨f.w, mem_basis _ (by simp)⟩
  let basis : Fin 5 → E := ![W,U,V,T,Z]
  have hcl : closure (Set.range basis) = ⊤ := by
    apply Subgroup.map_injective E.subtype_injective
    rw [MonoidHom.map_closure]
    have hi : E.subtype '' Set.range basis = ({z,n.t,n.v,f.u,f.w} : Set G) := by
      simp [basis, Matrix.range_cons, Set.image_insert_eq, Z,T,V,U,W]
    rw [hi, f.derived_basis, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have square (x : E) : x*x=1 := by
    exact (pow_two x).symm.trans
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) x)
  obtain ⟨b,hb⟩ := Theory.GroupTheory.exists_bool_prod_of_mem_closure_range basis
    (fun i => square (basis i)) (show (⟨s,hs⟩ : E) ∈ closure (Set.range basis) by rw [hcl]; trivial)
  refine ⟨b 0,b 1,b 2,b 3,b 4, ?_⟩
  have hp (i : Bool) (x : E) : (if i then x else 1) = x ^ i.toNat := by cases i <;> simp
  have hb' := congrArg (fun x : E => (x:G)) hb
  simpa [Fin.prod_univ_succ, basis, hp, Z,T,V,U,W, mul_assoc] using hb'

set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
/-- Squaring the a-image eliminates its t coefficient. -/
public theorem ParrottCentralizerInvolutionData.a_image_four_coefficients [Finite G]
    (f : ParrottCentralizerInvolutionData n)
    (h : ParrottCentralizerHypotheses z) :
    ∃ i j k m : Bool, f.r⁻¹*f.a*f.r = f.d*f.w^i.toNat*f.u^j.toNat*n.v^k.toNat*z^m.toNat := by
  obtain ⟨i,j,k,l,m,he⟩ := f.derived_binary_expansion h (f.a_image_mod_derived h)
  have ha : f.r⁻¹*f.a*f.r = f.d*f.w^i.toNat*f.u^j.toNat*n.v^k.toNat*n.t^l.toNat*z^m.toNat := by
    have he' := congrArg (fun q => f.d*q) he
    simpa only [mul_assoc, mul_inv_cancel_left] using he'
  have hz : z ≠ 1 := by
    intro hh
    have ho := h.involution
    rw [hh, orderOf_one] at ho
    omega
  have hs : (f.r⁻¹*f.a*f.r)^2=1 := by
    change act f.r f.a ^ 2 = 1
    rw [← map_pow, f.a_sq, map_one]
  have sq_z : z*z=1 := by simpa only [pow_two] using f.z_sq
  have sq_t : n.t*n.t=1 := by simpa only [pow_two] using f.t_sq
  have sq_v : n.v*n.v=1 := by simpa only [pow_two] using f.v_sq
  have sq_u : f.u*f.u=1 := by simpa only [pow_two] using f.u_sq
  have sq_w : f.w*f.w=1 := by simpa only [pow_two] using f.w_sq
  have swap_zt := f.comm_zt.eq
  have swap_zv := f.comm_zv.eq
  have swap_zu := f.comm_zu.eq
  have swap_zw := f.comm_zw.eq
  have swap_tv := f.comm_tv.eq
  have swap_tu := f.comm_tu.eq
  have swap_tw := f.comm_tw.eq
  have swap_vu := f.comm_vu.eq
  have swap_vw := f.comm_vw.eq
  have swap_uw := f.comm_uw.eq
  have sq_d : f.d*f.d=1 := by simpa only [pow_two] using f.d_sq
  have swap_zd := f.comm_zd.eq
  have swap_vd := f.toParrottSylowGeneratorData.core_commute_d_v.symm.eq
  have swap_ud := ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq08_du).symm.eq
  have swap_wd := ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq07_dw).symm.eq
  have swap_td := revswap ((Tits.parrottCommutator_eq_iff _ _ _).mp f.eq03_dt)
  simp only [sqinv f.z_sq] at swap_td
  have hl : l=false := by
    cases l
    · rfl
    · exfalso
      rw [ha] at hs
      cases i <;> cases j <;> cases k <;> cases m
      all_goals
        simp only [Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one, mul_one, pow_two] at hs
        simp only [mul_assoc,
      mul_one, one_mul, sq_z, tail sq_z, sq_t, tail sq_t, sq_v, tail sq_v, sq_u, tail sq_u,
      sq_w, tail sq_w, swap_zt, tail swap_zt, swap_zv, tail swap_zv, swap_zu, tail swap_zu,
      swap_zw, tail swap_zw, swap_tv, tail swap_tv, swap_tu, tail swap_tu, swap_tw, tail
      swap_tw, swap_vu, tail swap_vu, swap_vw, tail swap_vw, swap_uw, tail swap_uw, sq_d, tail
      sq_d, swap_zd, tail swap_zd, swap_vd, tail swap_vd, swap_ud, tail swap_ud, swap_wd, tail
      swap_wd, swap_td, tail swap_td] at hs
      all_goals exact hz hs
  subst l
  exact ⟨i,j,k,m,by simpa only [Bool.toNat_false, pow_zero, mul_one] using ha⟩


set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
/-- Transporting [b,c] = uv determines the u exponent in the candidate c-image.
The exponent is α xor β, rather than α in the current parameter interface. -/
public theorem ParrottCentralizerInvolutionData.c_action_exponent_constraint
    (f : ParrottCentralizerInvolutionData n)
    (h : ParrottCentralizerHypotheses z) (α β ε δ γ : Bool)
    (Rb : f.r⁻¹ * f.b * f.r = f.d * f.c * f.b * f.w ^ (!α).toNat *
      (n.v * n.t) ^ (α.xor β).toNat * z ^ γ.toNat)
    (Rc : f.r⁻¹ * f.c * f.r = f.c * f.d * f.a * f.w ^ β.toNat *
      f.u ^ ε.toNat * n.t ^ β.toNat * z ^ δ.toNat) : ε = α.xor β := by
  have hz : z ≠ 1 := by
    intro hh
    have ho := h.involution
    rw [hh, orderOf_one] at ho
    omega
  change act f.r f.b = _ at Rb
  change act f.r f.c = _ at Rc
  have Ru : act f.r f.u = f.u := f.eq22_ur
  have Rv : act f.r n.v = f.u*n.v := f.eq21_vr
  have hh := congrArg (act f.r) ((Tits.parrottCommutator_eq_iff _ _ _).mp f.eq15_bc)
  simp only [map_mul, Rb,Rc,Ru,Rv] at hh
  -- Collection rules for the core, with the elementary tail ordered w,u,v,t,z.
  have sq_z : z * z = 1 := by simpa only [pow_two] using f.z_sq
  have sq_t : n.t * n.t = 1 := by simpa only [pow_two] using f.t_sq
  have sq_v : n.v * n.v = 1 := by simpa only [pow_two] using f.v_sq
  have sq_u : f.u * f.u = 1 := by simpa only [pow_two] using f.u_sq
  have sq_w : f.w * f.w = 1 := by simpa only [pow_two] using f.w_sq
  have sq_a : f.a * f.a = 1 := by simpa only [pow_two] using f.a_sq
  have sq_d : f.d * f.d = 1 := by simpa only [pow_two] using f.d_sq
  have sq_b : f.b * f.b = n.v := by simpa only [pow_two] using f.eq03_b
  have sq_c : f.c * f.c = f.w * f.u := by simpa only [pow_two] using f.eq13
  have dv : f.d * n.v = n.v * f.d := by
    calc
      f.d * n.v = n.v⁻¹ * f.d := by
        rw [← f.eq03_db]
        simp only [Tits.parrottCommutator, mul_inv_rev, inv_inv, sqinv f.d_sq]
        group
        simp only [mul_assoc, sq_d, one_mul, mul_one]
      _ = n.v * f.d := by rw [sqinv f.v_sq]
  have bv : Commute f.b n.v := by
    rw [← f.eq03_b]
    exact Commute.self_pow f.b 2
  have swap_zt := f.comm_zt.eq
  have swap_zv := f.comm_zv.eq
  have swap_zu := f.comm_zu.eq
  have swap_zw := f.comm_zw.eq
  have swap_tv := f.comm_tv.eq
  have swap_tu := f.comm_tu.eq
  have swap_tw := f.comm_tw.eq
  have swap_vu := f.comm_vu.eq
  have swap_vw := f.comm_vw.eq
  have swap_uw := f.comm_uw.eq
  have swap_az := f.comm_az.symm.eq
  have swap_at := f.comm_at.symm.eq
  have swap_av := f.comm_av.symm.eq
  have swap_au := f.comm_au.symm.eq
  have swap_zb := f.comm_zb.eq
  have swap_zc := f.comm_zc.eq
  have swap_zd := f.comm_zd.eq
  have swap_bt := f.comm_bt.symm.eq
  have swap_dv := dv.symm
  have swap_bv := bv.symm.eq
  have swap_bw := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq02_bw
  have swap_bw := revswap swap_bw
  simp only [inv_one, mul_one] at swap_bw
  have swap_aw := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq02_aw
  have swap_aw := revswap swap_aw
  simp only [sqinv f.z_sq] at swap_aw
  have swap_bu := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq02_bu
  have swap_bu := revswap swap_bu
  simp only [sqinv f.z_sq] at swap_bu
  have swap_db := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq03_db
  have swap_db := revswap swap_db
  simp only [sqinv f.v_sq] at swap_db
  have swap_dt := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq03_dt
  have swap_dt := revswap swap_dt
  simp only [sqinv f.z_sq] at swap_dt
  have swap_ab := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq05_ab
  have swap_dw := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq07_dw
  have swap_dw := revswap swap_dw
  simp only [inv_one, mul_one] at swap_dw
  have swap_du := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq08_du
  have swap_du := revswap swap_du
  simp only [inv_one, mul_one] at swap_du
  have swap_cu := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq09_cu
  have swap_cu := revswap swap_cu
  simp only [inv_one, mul_one] at swap_cu
  have swap_cw := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq09_cw
  have swap_cw := revswap swap_cw
  simp only [inv_one, mul_one] at swap_cw
  have swap_ct := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq10_ct
  have swap_ct := revswap swap_ct
  simp only [inv_one, mul_one] at swap_ct
  have swap_cv := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq10_cv
  have swap_cv := revswap swap_cv
  simp only [sqinv f.z_sq] at swap_cv
  have swap_ad := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq11_ad
  have swap_ac := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq12_ac
  have swap_cd := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq14_cd
  have swap_bc := (Tits.parrottCommutator_eq_iff _ _ _).mp f.eq15_bc
  have inv_b : f.b⁻¹ = f.b * n.v := by
    apply inv_eq_of_mul_eq_one_right
    simp only [← mul_assoc, sq_b, sq_v]
  have inv_c : f.c⁻¹ = f.c * f.u * f.w := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, ← mul_assoc, sq_c]
    simp only [mul_assoc, tail sq_u, one_mul, sq_w]

  cases α <;> cases β <;> cases ε <;> cases δ <;> cases γ
  all_goals first | rfl | exfalso
  all_goals
    simp only [Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
      Bool.toNat_true, Bool.toNat_false, pow_zero, pow_one, mul_one] at hh
    simp only [and_self, mul_assoc, one_mul, mul_one, mul_inv_rev,
  inv_b, inv_c, sqinv f.z_sq, sqinv f.t_sq, sqinv f.v_sq,
  sqinv f.u_sq, sqinv f.w_sq, sqinv f.a_sq, sqinv f.d_sq, tail swap_zt,
  swap_zt, tail swap_zv, swap_zv, tail swap_zu, swap_zu,
  tail swap_zw, swap_zw, tail swap_tv, swap_tv, tail swap_tu,
  swap_tu, tail swap_tw, swap_tw, tail swap_vu, swap_vu,
  tail swap_vw, swap_vw, tail swap_uw, swap_uw, tail swap_az,
  swap_az, tail swap_at, swap_at, tail swap_av, swap_av,
  tail swap_au, swap_au, tail swap_zb, swap_zb, tail swap_zc,
  swap_zc, tail swap_zd, swap_zd, tail swap_bt, swap_bt,
  tail swap_dv, swap_dv, tail swap_bv, swap_bv, tail swap_bw,
  swap_bw, tail swap_aw, swap_aw, tail swap_bu, swap_bu,
  tail swap_db, swap_db, tail swap_dt, swap_dt, tail swap_ab,
  swap_ab, tail swap_dw, swap_dw, tail swap_du, swap_du,
  tail swap_cu, swap_cu, tail swap_cw, swap_cw, tail swap_ct,
  swap_ct, tail swap_cv, swap_cv, tail swap_ad, swap_ad,
  tail swap_ac, swap_ac, tail swap_cd, swap_cd, tail swap_bc,
  swap_bc, tail sq_z, sq_z, tail sq_t, sq_t,
  tail sq_v, sq_v, tail sq_u, sq_u, tail sq_w,
  sq_w, tail sq_a, sq_a, tail sq_d, sq_d,
  tail sq_b, sq_b, tail sq_c, sq_c] at hh
  all_goals
    have he : z=1 := by simpa using hh
    exact hz he


/-- The current parameter interface forces the first source a-image coset. -/
public theorem ParrottCentralizerInvolutionData.action_parameter_beta_false
    (f : ParrottCentralizerInvolutionData n)
    (h : ParrottCentralizerHypotheses z) (α β δ γ : Bool)
    (hp : f.HasActionParameters α β δ γ) : β = false := by
  have he := f.c_action_exponent_constraint h α β α δ γ hp.2.2.2 hp.2.2.1
  cases α <;> cases β
  · rfl
  · exact Bool.noConfusion he
  · rfl
  · exact Bool.noConfusion he


/-- The second source a-image coset cannot satisfy the current parameter
interface, regardless of the four parameters chosen. -/
public theorem ParrottCentralizerInvolutionData.not_exists_action_parameters_of_second_a_coset
    (f : ParrottCentralizerInvolutionData n) (h : ParrottCentralizerHypotheses z)
    (α δ : Bool)
    (ha : f.r⁻¹ * f.a * f.r = f.d * f.u ^ α.toNat * n.v * z ^ δ.toNat) :
    ¬ ∃ α' β' δ' γ' : Bool, f.HasActionParameters α' β' δ' γ' := by
  rintro ⟨α', β', δ', γ', hp⟩
  have hβ := f.action_parameter_beta_false h α' β' δ' γ' hp
  subst β'
  have he : f.u ^ α.toNat * n.v * z ^ δ.toNat =
      f.u ^ α'.toNat * z ^ δ'.toNat := by
    apply mul_left_cancel (a := f.d)
    simpa only [Bool.toNat_false, pow_zero, mul_one, mul_assoc] using ha.symm.trans hp.1
  have hcu : Commute f.c f.u := (Tits.parrottCommutator_eq_one_iff _ _).mp f.eq09_cu
  have hcz : Commute f.c z := f.comm_zc.symm
  have hc : Commute f.c (f.u ^ α.toNat * n.v * z ^ δ.toNat) := by
    rw [he]
    exact (hcu.pow_right α'.toNat).mul_right (hcz.pow_right δ'.toNat)
  have hc' : Commute f.c (f.u ^ α.toNat * n.v) := by
    simpa only [mul_inv_cancel_right] using hc.mul_right (hcz.pow_right δ.toNat).inv_right
  have hcv : Commute f.c n.v := by
    simpa only [inv_mul_cancel_left] using (hcu.pow_right α.toNat).inv_right.mul_right hc'
  have hz : z = 1 := f.eq10_cv.symm.trans
    ((Tits.parrottCommutator_eq_one_iff _ _).mpr hcv)
  have ho := h.involution
  rw [hz, orderOf_one] at ho
  omega


set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
/-- The d-image is determined by the four a-image coefficients and r² = 1. -/
public theorem ParrottCentralizerInvolutionData.d_image_of_a_four_coefficients
    (f : ParrottCentralizerInvolutionData n) (i j k m : Bool)
    (ha : f.r⁻¹*f.a*f.r = f.d*f.w^i.toNat*f.u^j.toNat*n.v^k.toNat*z^m.toNat) :
    f.r⁻¹*f.d*f.r = f.a*f.u^(j.xor k).toNat*n.v^(i.xor k).toNat*
      n.t^i.toNat*z^(i.xor m).toNat := by
  change act f.r f.a = _ at ha
  have Rz := act_comm f.comm_zr
  have Rv : act f.r n.v = _ := f.eq21_vr
  have Ru : act f.r f.u = _ := f.eq22_ur
  have Rw : act f.r f.w = _ := f.eq22_wr
  have hrr (x : G) : act f.r (act f.r x) = x := by
    change f.r⁻¹*(f.r⁻¹*x*f.r)*f.r=x
    have rr : f.r*f.r=1 := by simpa only [pow_two] using f.eq20_r
    rw [sqinv f.eq20_r]
    calc
      f.r * (f.r*x*f.r) * f.r = (f.r*f.r)*x*(f.r*f.r) := by group
      _ = x := by rw [rr]; simp
  have hh := congrArg (act f.r) ha
  rw [hrr] at hh
  simp only [map_mul, map_pow, Rz, Rv, Ru, Rw] at hh
  have hd : act f.r f.d = f.a *
      ((n.v*n.t*z)^i.toNat*f.u^j.toNat*(f.u*n.v)^k.toNat*z^m.toNat)⁻¹ := by
    apply (eq_mul_inv_iff_mul_eq).mpr
    simpa only [mul_assoc] using hh.symm
  change act f.r f.d = _
  rw [hd]
  have sq_z : z*z=1 := by simpa only [pow_two] using f.z_sq
  have sq_t : n.t*n.t=1 := by simpa only [pow_two] using f.t_sq
  have sq_v : n.v*n.v=1 := by simpa only [pow_two] using f.v_sq
  have sq_u : f.u*f.u=1 := by simpa only [pow_two] using f.u_sq
  have sq_w : f.w*f.w=1 := by simpa only [pow_two] using f.w_sq
  have swap_zt := f.comm_zt.eq
  have swap_zv := f.comm_zv.eq
  have swap_zu := f.comm_zu.eq
  have swap_zw := f.comm_zw.eq
  have swap_tv := f.comm_tv.eq
  have swap_tu := f.comm_tu.eq
  have swap_tw := f.comm_tw.eq
  have swap_vu := f.comm_vu.eq
  have swap_vw := f.comm_vw.eq
  have swap_uw := f.comm_uw.eq

  cases i <;> cases j <;> cases k <;> cases m
  all_goals
    simp only [Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
      Bool.toNat_false, Bool.toNat_true, pow_zero, pow_one, mul_one,
      inv_one, mul_inv_rev, sqinv f.z_sq, sqinv f.t_sq, sqinv f.v_sq,
      sqinv f.u_sq] <;>
    simp only [mul_assoc,
      mul_one, one_mul, sq_z, tail sq_z, sq_t, tail sq_t, sq_v, tail sq_v, sq_u, tail sq_u,
      sq_w, tail sq_w, swap_zt, tail swap_zt, swap_zv, tail swap_zv, swap_zu, tail swap_zu,
      swap_zw, tail swap_zw, swap_tv, tail swap_tv, swap_tu, tail swap_tu, swap_tw, tail
      swap_tw, swap_vu, tail swap_vu, swap_vw, tail swap_vw, swap_uw, tail swap_uw]

end Stellmacher.Recognition
