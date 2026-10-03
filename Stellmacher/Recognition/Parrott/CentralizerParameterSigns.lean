module

public import Stellmacher.Recognition.Parrott.CentralizerCompatibleParameters

/-!
# Removing the central signs in Parrott's compatible action

Conjugating only r by t changes (δ,γ) to (!δ,!γ), and conjugating it by v
changes (δ,γ) to (δ,!γ). These operations retain every Sylow coordinate.
The calculations use the corrected u exponent α xor β in the c-image.

Both conjugators lie in T and commute with y and the elementary derived
subgroup. Thus they preserve generation of the actual centralizer, the
fifth-power relation, and equations (20)–(22). A single transport construction
also checks the order, ambient conjugacy class, and z-centrality of the new r.
The two sign operations then give a compatible action with δ = γ = false,
without changing β or requiring any additional global hypotheses.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.680–681, the central-factor replacements preceding (23).
-/

open Subgroup
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

private def act (k : G) : G →* G where
  toFun g := k⁻¹ * g * k
  map_one' := by simp
  map_mul' _ _ := by simp [mul_assoc]

private theorem act_fixed {k g : G} (h : Commute k g) : act k g = g := by
  change k⁻¹ * g * k = g
  rw [mul_assoc, ← h.eq]; simp

private theorem act_conjugate {k g : G} (h : Commute k g) (r : G) :
    act (act k r) g = act k (act r g) := by
  have hh : k * g * k⁻¹ = g := by rw [h.eq]; group
  change (k⁻¹ * r * k)⁻¹ * g * (k⁻¹ * r * k) = k⁻¹ * (r⁻¹ * g * r) * k
  calc
    _ = k⁻¹ * r⁻¹ * (k * g * k⁻¹) * r * k := by group
    _ = _ := by rw [hh]; group

private theorem sup_zpowers_conjugate (T : Subgroup G) (r k : G) (hk : k ∈ T) :
    T ⊔ zpowers (act k r) = T ⊔ zpowers r := by
  apply le_antisymm
  · apply sup_le le_sup_left
    apply zpowers_le.mpr
    exact mul_mem (mul_mem (inv_mem (mem_sup_left hk)) (mem_sup_right (mem_zpowers r)))
      (mem_sup_left hk)
  · apply sup_le le_sup_left
    apply zpowers_le.mpr
    have hh : k * act k r * k⁻¹ = r := by dsimp [act]; group
    have hm : k * act k r * k⁻¹ ∈ T ⊔ zpowers (act k r) :=
      mul_mem (mul_mem (mem_sup_left hk) (mem_sup_right (mem_zpowers _)))
        (inv_mem (mem_sup_left hk))
    simpa only [hh] using hm

private theorem sqinv {g : G} (h : g ^ 2 = 1) : g⁻¹ = g :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h)

private theorem act_conjugate_sq {k : G} (hk : k ^ 2 = 1) (r g : G) :
    act (act k r) g = act k (act r (act k g)) := by
  dsimp [act]
  simp only [mul_inv_rev, sqinv hk, mul_assoc]

private theorem act_commutator {g k q : G} (h : Tits.parrottCommutator g k = q) :
    act k g = g * q := by
  have hh := (Tits.parrottCommutator_eq_iff _ _ _).mp h
  change k⁻¹ * g * k = g * q
  rw [mul_assoc, hh]
  group

private theorem tail {a b c : G} (h : a * b = c) (k : G) :
    a * (b * k) = c * k := by rw [← mul_assoc, h]

namespace ParrottCentralizerInvolutionData
variable (f : ParrottCentralizerInvolutionData n)

/-- Conjugate r by an element of T fixing y and the elementary derived basis. -/
private def conjugateFrame (k : G) (hk : k ∈ e.sylow)
    (hy : Commute k f.y) (hz : Commute k z)
    (ht : Commute k n.t) (hv : Commute k n.v)
    (hu : Commute k f.u) (hw : Commute k f.w) :
    ParrottCentralizerInvolutionData n where
  toParrottSylowGeneratorData := f.toParrottSylowGeneratorData
  r := act k f.r
  centralizer_generators := (sup_zpowers_conjugate _ _ _ hk).trans f.centralizer_generators
  r_order := by
    simpa only [MulAut.conj_apply, inv_inv, act, MonoidHom.coe_mk, OneHom.coe_mk]
      using ((MulAut.conj k⁻¹).orderOf_eq f.r).trans f.r_order
  r_conjugate := (isConj_iff.mpr ⟨k, by dsimp [act]; group⟩).trans f.r_conjugate
  comm_zr := by
    have hh := f.comm_zr.map (act k)
    rwa [act_fixed hz] at hh
  eq20_r := by rw [← map_pow, f.eq20_r, map_one]
  eq20_ry := by
    rw [← act_fixed hy, ← map_mul, ← map_pow, f.eq20_ry, map_one]
  eq20_tr := by
    change act (act k f.r) n.t = _
    rw [act_conjugate ht]
    change act k (f.r⁻¹ * n.t * f.r) = _
    rw [f.eq20_tr, map_mul, map_mul, map_mul, act_fixed hw, act_fixed hu,
      act_fixed hv, act_fixed hz]
  eq21_vr := by
    change act (act k f.r) n.v = _
    rw [act_conjugate hv]
    change act k (f.r⁻¹ * n.v * f.r) = _
    rw [f.eq21_vr, map_mul, act_fixed hu, act_fixed hv]
  eq22_ur := by
    change act (act k f.r) f.u = _
    rw [act_conjugate hu]
    change act k (f.r⁻¹ * f.u * f.r) = _
    rw [f.eq22_ur, act_fixed hu]
  eq22_wr := by
    change act (act k f.r) f.w = _
    rw [act_conjugate hw]
    change act k (f.r⁻¹ * f.w * f.r) = _
    rw [f.eq22_wr, map_mul, map_mul, act_fixed hv, act_fixed ht, act_fixed hz]

private theorem commute_t_y : Commute n.t f.y := by
  have ht := ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq01_xt).symm
  have hh := (ht.pow_right 2).mul_right f.comm_zt.symm
  have hy : f.x ^ 2 * z = f.y := by
    rw [f.eq04, mul_assoc, ← pow_two, f.z_sq, mul_one]
  rwa [hy] at hh

private theorem commute_v_y : Commute n.v f.y := by
  rw [← f.eq03_b]
  exact ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq18_by).pow_left 2

private def conjugateT : ParrottCentralizerInvolutionData n :=
  f.conjugateFrame n.t f.toParrottSylowGeneratorData.local_mem_sylow.2.1
    f.commute_t_y f.comm_zt.symm (Commute.refl _) f.comm_tv f.comm_tu f.comm_tw

private def conjugateV : ParrottCentralizerInvolutionData n :=
  f.conjugateFrame n.v f.toParrottSylowGeneratorData.local_mem_sylow.2.2.1
    f.commute_v_y f.comm_zv.symm f.comm_tv.symm (Commute.refl _) f.comm_vu f.comm_vw

-- Conjugation by t fixes a,b,c and multiplies d by z.
set_option linter.unusedSimpArgs false in
private theorem conjugateT_parameters (β δ γ : Bool)
    (hp : f.HasCompatibleActionParameters true β δ γ) :
    f.conjugateT.HasCompatibleActionParameters true β (!δ) (!γ) := by
  have Tz := act_fixed f.comm_zt.symm
  have Tt := act_fixed (Commute.refl n.t)
  have Tv := act_fixed f.comm_tv
  have Tu := act_fixed f.comm_tu
  have Tw := act_fixed f.comm_tw
  have Ta := act_fixed f.comm_at.symm
  have Tb := act_fixed f.comm_bt.symm
  have Tc := act_fixed ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq10_ct).symm
  have Td := act_commutator f.eq03_dt
  have Rz := act_fixed f.comm_zr.symm
  have Ra : act f.r f.a = _ := hp.1
  have Rd : act f.r f.d = _ := hp.2.1
  have Rc : act f.r f.c = _ := hp.2.2.1
  have Rb : act f.r f.b = _ := hp.2.2.2
  change act (act n.t f.r) f.a = _ ∧ act (act n.t f.r) f.d = _ ∧
    act (act n.t f.r) f.c = _ ∧ act (act n.t f.r) f.b = _
  dsimp only [conjugateT, conjugateFrame]
  simp only [act_conjugate_sq f.t_sq, Ta, Tb, Tc, Td, map_mul, Ra, Rb, Rc, Rd, Rz]
  cases β <;> cases δ <;> cases γ
  all_goals
    simp only [Bool.toNat_true, Bool.toNat_false, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false, pow_one, pow_zero,
      map_mul, map_one, Tz, Tt, Tv, Tu, Tw, Ta, Tb, Tc, Td, one_mul, mul_one]
    simp only [mul_assoc, f.comm_az.symm.eq, tail f.comm_az.symm.eq,
      f.comm_zb.eq, tail f.comm_zb.eq, f.comm_zc.eq, tail f.comm_zc.eq, f.comm_zu.eq, tail f.comm_zu.eq,
      f.comm_zw.eq, tail f.comm_zw.eq, f.comm_zv.eq, tail f.comm_zv.eq,
      f.comm_zt.eq, tail f.comm_zt.eq,
      ← pow_two, f.z_sq, mul_one, and_self, eq_self_iff_true]

-- Conjugation by v fixes a,b,d and multiplies c by z.
set_option linter.unusedSimpArgs false in
private theorem conjugateV_parameters (β δ γ : Bool)
    (hp : f.HasCompatibleActionParameters true β δ γ) :
    f.conjugateV.HasCompatibleActionParameters true β δ (!γ) := by
  have hd : f.d⁻¹ = f.d := sqinv f.d_sq
  have hv : n.v⁻¹ = n.v := sqinv f.v_sq
  have heq : f.d * n.v = f.b⁻¹ * f.d * f.b := by
    rw [← f.eq03_db]
    simp only [Tits.parrottCommutator]
    group
  have heq' := congrArg Inv.inv heq
  simp only [mul_inv_rev, hd, hv, inv_inv] at heq'
  have dv : Commute f.d n.v := heq.trans (by simpa only [mul_assoc] using heq'.symm)
  have bv : Commute f.b n.v := by rw [← f.eq03_b]; exact Commute.self_pow _ _
  have Vz := act_fixed f.comm_zv.symm
  have Vt := act_fixed f.comm_tv.symm
  have Vv := act_fixed (Commute.refl n.v)
  have Vu := act_fixed f.comm_vu
  have Vw := act_fixed f.comm_vw
  have Va := act_fixed f.comm_av.symm
  have Vb := act_fixed bv.symm
  have Vc := act_commutator f.eq10_cv
  have Vd := act_fixed dv.symm
  have Rz := act_fixed f.comm_zr.symm
  have Ra : act f.r f.a = _ := hp.1
  have Rd : act f.r f.d = _ := hp.2.1
  have Rc : act f.r f.c = _ := hp.2.2.1
  have Rb : act f.r f.b = _ := hp.2.2.2
  change act (act n.v f.r) f.a = _ ∧ act (act n.v f.r) f.d = _ ∧
    act (act n.v f.r) f.c = _ ∧ act (act n.v f.r) f.b = _
  dsimp only [conjugateV, conjugateFrame]
  simp only [act_conjugate_sq f.v_sq, Va, Vb, Vc, Vd, map_mul, Ra, Rb, Rc, Rd, Rz]
  cases β <;> cases δ <;> cases γ
  all_goals
    simp only [Bool.toNat_true, Bool.toNat_false, Bool.xor_true, Bool.xor_false, Bool.not_true, Bool.not_false, pow_one, pow_zero,
      map_mul, map_one, Vz, Vt, Vv, Vu, Vw, Va, Vb, Vc, Vd, one_mul, mul_one]
    simp only [mul_assoc, f.comm_az.symm.eq, tail f.comm_az.symm.eq,
      f.comm_zb.eq, tail f.comm_zb.eq, f.comm_zd.eq, tail f.comm_zd.eq,
      f.comm_zu.eq, tail f.comm_zu.eq, f.comm_zw.eq, tail f.comm_zw.eq,
      f.comm_zv.eq, tail f.comm_zv.eq, f.comm_zt.eq, tail f.comm_zt.eq,
      ← pow_two, f.z_sq, mul_one, and_self, eq_self_iff_true]

/-- Remove both central signs by conjugating only r. The entire supplied
Sylow frame, not just the elementary and normalizer data, is retained. -/
public theorem exists_compatible_action_parameters_normalized_signs_same_frame
    (β δ γ : Bool) (hp : f.HasCompatibleActionParameters true β δ γ) :
    ∃ f' : ParrottCentralizerInvolutionData n,
      f'.toParrottSylowGeneratorData = f.toParrottSylowGeneratorData ∧
      f'.HasCompatibleActionParameters true β false false := by
  cases δ <;> cases γ
  · exact ⟨f, rfl, hp⟩
  · exact ⟨f.conjugateV, rfl, f.conjugateV_parameters β false true hp⟩
  · exact ⟨f.conjugateT.conjugateV, rfl,
      f.conjugateT.conjugateV_parameters β false true
        (f.conjugateT_parameters β true false hp)⟩
  · exact ⟨f.conjugateT, rfl, f.conjugateT_parameters β true true hp⟩

/-- Every supplied compatible true-α action admits zero central signs,
with the same noncentral parameter β and the original e,n (hence F,T,z,t,v). -/
public theorem exists_compatible_action_parameters_normalized_signs
    (β δ γ : Bool) (hp : f.HasCompatibleActionParameters true β δ γ) :
    ∃ f' : ParrottCentralizerInvolutionData n,
      f'.HasCompatibleActionParameters true β false false := by
  obtain ⟨f', _, hp'⟩ :=
    f.exists_compatible_action_parameters_normalized_signs_same_frame β δ γ hp
  exact ⟨f', hp'⟩

end ParrottCentralizerInvolutionData
end Stellmacher.Recognition
