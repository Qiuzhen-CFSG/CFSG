module
public import Stellmacher.Recognition.Parrott.SylowCoreGeometry

/-!
# The outer action on Parrott's initial core frame

The equations through (10) determine the action on J/E without any of
(11)–(15). Compare right conjugation on the transformed elementary basis
z,t,vt,uv,wu. Since C_G(E)=E, equal actions give equal cosets. This gives
[b,x] ∈ aE, [c,x] ∈ abE, [d,x] ∈ abcE, and (cd)^x ∈ dE.

Squares in one E-coset agree modulo ⟨z⟩ because E is elementary and equals
the second center of J. Consequently (cd)² ∈ ⟨z⟩, since d²=1. The module
also supplies the antidiagonal core/derived pairing, derived membership of
commutators and squares, and the commutation of d with [a,d] and c².
Every supplied coordinate is retained. No completed generator frame, core
coset alternative, or explicit fusion census is assumed.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed pp.678–679, equations (1)–(10) and the following coset observations.
The comparison on the transformed basis adapts the proof pattern in
Theory.SpecificGroups.Tits.RecognitionSylowOuterCosets to the initial frame.
-/

open Subgroup
open scoped IsMulCommutative
namespace Stellmacher.Recognition.ParrottSylowInitialData
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
set_option quotPrecheck false in
local notation "H" => centralizer ({z} : Set G)
set_option quotPrecheck false in
local notation "J" => (pCore 2 H).map (H).subtype
set_option quotPrecheck false in
local notation "E" => (commutator (pCore 2 H)).map ((H).subtype.comp (pCore 2 H).subtype)

/-- The five supplied elementary coordinates belong to F. -/
public theorem basis_mem_elementary (f : ParrottSylowInitialData n) :
    ∀ g ∈ ({z, n.t, n.v, f.u, f.a} : Set G), g ∈ e.F := by
  intro g hg
  rw [← f.elementary_basis]
  exact subset_closure hg

/-- Elements of the supplied elementary subgroup commute. -/
public theorem commute_of_mem_elementary (_f : ParrottSylowInitialData n)
    {g k : G} (hg : g ∈ e.F) (hk : k ∈ e.F) : Commute g k := by
  let : IsElementaryAbelian 2 e.F := e.elementary
  exact setLike_mul_comm hg hk

/-- The relation [d,b]=v, with d and v of square one, forces [d,v]=1. -/
public theorem core_commute_d_v (f : ParrottSylowInitialData n) : Commute f.d n.v := by
  have hd : f.d⁻¹ = f.d := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using f.d_sq)
  have hv : n.v⁻¹ = n.v := inv_eq_of_mul_eq_one_right
    (by have hv : n.v ^ 2 = 1 := n.v_order ▸ pow_orderOf_eq_one n.v
        simpa only [pow_two] using hv)
  have heq : f.d * n.v = f.b⁻¹ * f.d * f.b := by
    rw [← f.eq03_db]
    simp only [Tits.parrottCommutator]
    group
  have heq' := congrArg Inv.inv heq
  simp only [mul_inv_rev, hd, hv, inv_inv] at heq'
  exact heq.trans (by simpa only [mul_assoc] using heq'.symm)

private def R (g : G) : G ≃* G := MulAut.conj g⁻¹
private theorem R_mul (g k s : G) : R (g*k) s = R k (R g s) := by
  simp [R, mul_assoc]
private theorem R_comm {g k : G} (h : Commute g k) : R g k = k := by
  simp only [R, MulAut.conj_apply, inv_inv]
  rw [mul_assoc, h.symm.eq, inv_mul_cancel_left]
private theorem R_pc {g k r : G}
    (hr : Tits.parrottCommutator g k = r) (hr2 : r^2=1) : R g k=k*r := by
  have hs := (Tits.parrottCommutator_eq_iff _ _ _).mp hr
  have hrr : r*r=1 := by simpa only [pow_two] using hr2
  have heq := congrArg (fun p : G => g⁻¹*p*r) hs
  simpa only [R, MulAut.conj_apply, inv_inv, mul_assoc,
    inv_mul_cancel_left, hrr, mul_one] using heq.symm

private theorem outer_derived_closure (z t v u w : G) :
    closure ({z,t,v*t,u*v,w*u} : Set G) = closure ({z,t,v,u,w} : Set G) := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hz : z ∈ closure ({z,t,v,u,w} : Set G) := subset_closure (by simp)
    have ht : t ∈ closure ({z,t,v,u,w} : Set G) := subset_closure (by simp)
    have hv : v ∈ closure ({z,t,v,u,w} : Set G) := subset_closure (by simp)
    have hu : u ∈ closure ({z,t,v,u,w} : Set G) := subset_closure (by simp)
    have hw : w ∈ closure ({z,t,v,u,w} : Set G) := subset_closure (by simp)
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · exact hz
    · exact ht
    · exact mul_mem hv ht
    · exact mul_mem hu hv
    · exact mul_mem hw hu
  · apply (closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    let L := closure ({z,t,v*t,u*v,w*u} : Set G)
    have hz : z ∈ L := subset_closure (by simp)
    have ht : t ∈ L := subset_closure (by simp)
    have hv : v ∈ L := (L.mul_mem_cancel_right ht).mp (subset_closure (by simp))
    have hu : u ∈ L := (L.mul_mem_cancel_right hv).mp (subset_closure (by simp))
    have hw : w ∈ L := (L.mul_mem_cancel_right hu).mp (subset_closure (by simp))
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> assumption

private theorem discrepancy_commute (P : G ≃* G) {g r s : G}
    (h : R r (P s) = P (R g s)) : Commute (P s) (P g*r⁻¹) := by
  simp only [R, MulAut.conj_apply, inv_inv] at h
  simp only [map_mul, map_inv] at h
  have he := congrArg (fun q => P g * q * r⁻¹) h
  change P s * (P g*r⁻¹) = (P g*r⁻¹) * P s
  simpa only [mul_assoc, mul_inv_cancel_right, mul_inv_cancel_left, mul_inv_cancel, mul_one] using he.symm

set_option linter.unusedSimpArgs false in
/-- The outer images of b,c,d and cd, before any core cosets are selected. -/
public theorem outer_images_mod_derived [Finite G] (f : ParrottSylowInitialData n)
    (h : ParrottCentralizerHypotheses z) :
    f.x⁻¹*f.b*f.x / (f.b*f.a) ∈ E ∧
    f.x⁻¹*f.c*f.x / (f.c*f.a*f.b) ∈ E ∧
    f.x⁻¹*f.d*f.x / (f.d*f.a*f.b*f.c) ∈ E ∧
    f.x⁻¹*(f.c*f.d)*f.x / f.d ∈ E := by
  let P := R f.x
  have hzs : z^2=1 := h.involution ▸ pow_orderOf_eq_one z
  have hts : n.t^2=1 := n.t_order ▸ pow_orderOf_eq_one n.t
  have hvs : n.v^2=1 := n.v_order ▸ pow_orderOf_eq_one n.v
  have hus : f.u^2=1 := by
    let : IsElementaryAbelian 2 e.F := e.elementary
    exact elemPow_eq_one_of_isElementaryAbelian _ (f.basis_mem_elementary _ (by simp))
  have hxH : f.x ∈ H := e.sylow_le_centralizer
    (f.sylow_eq.symm ▸ mem_sup_left (mem_zpowers f.x))
  have hz : P z = z := R_comm (mem_centralizer_singleton_iff.mp hxH)
  have ht : P n.t = n.t := R_comm ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq01_xt)
  have hv : P n.v = n.v*n.t := R_pc f.eq01_xv hts
  have hu : P f.u = f.u*n.v := R_pc f.eq01_xu hvs
  have hw : P f.w = f.w*f.u := R_pc f.eq01_xw hus
  have az : R f.a z = z := R_comm (f.commute_z_of_mem_core
    (f.generators_mem_core f.a (by simp))).symm
  have bz : R f.b z = z := R_comm (f.commute_z_of_mem_core
    (f.generators_mem_core f.b (by simp))).symm
  have cz : R f.c z = z := R_comm (f.commute_z_of_mem_core
    (f.generators_mem_core f.c (by simp))).symm
  have dz : R f.d z = z := R_comm (f.commute_z_of_mem_core
    (f.generators_mem_core f.d (by simp))).symm
  have at_ : R f.a n.t = n.t := R_comm (f.commute_of_mem_elementary
    (f.basis_mem_elementary _ (by simp)) (f.basis_mem_elementary _ (by simp)))
  have av : R f.a n.v = n.v := R_comm (f.commute_of_mem_elementary
    (f.basis_mem_elementary _ (by simp)) (f.basis_mem_elementary _ (by simp)))
  have au : R f.a f.u = f.u := R_comm (f.commute_of_mem_elementary
    (f.basis_mem_elementary _ (by simp)) (f.basis_mem_elementary _ (by simp)))
  have aw := R_pc f.eq02_aw hzs
  have bt := R_comm f.comm_bt
  have bv : R f.b n.v = n.v := R_comm (by rw [← f.eq03_b]; exact Commute.self_pow _ _)
  have bu := R_pc f.eq02_bu hzs
  have bw := R_comm ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq02_bw)
  have ct := R_comm ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq10_ct)
  have cv := R_pc f.eq10_cv hzs
  have cu := R_comm ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq09_cu)
  have cw := R_comm ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq09_cw)
  have dt := R_pc f.eq03_dt hzs
  have dv := R_comm f.core_commute_d_v
  have du := R_comm ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq08_du)
  have dw := R_comm ((Tits.parrottCommutator_eq_one_iff _ _).mp f.eq07_dw)
  have step (g r : G)
      (hs : ∀ q ∈ ({z,n.t,n.v,f.u,f.w} : Set G), R r (P q) = P (R g q)) :
      P g/r ∈ E := by
    rw [← parrott_derived_centralizer z h, ← f.derived_basis,
      ← outer_derived_closure, centralizer_closure]
    apply mem_centralizer_iff.mpr
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · simpa only [hz, div_eq_mul_inv] using (discrepancy_commute P (hs q (by simp))).eq
    · simpa only [ht, div_eq_mul_inv] using (discrepancy_commute P (hs n.t (by simp))).eq
    · simpa only [hv, div_eq_mul_inv] using (discrepancy_commute P (hs n.v (by simp))).eq
    · simpa only [hu, div_eq_mul_inv] using (discrepancy_commute P (hs f.u (by simp))).eq
    · simpa only [hw, div_eq_mul_inv] using (discrepancy_commute P (hs f.w (by simp))).eq
  have hzt := f.commute_z_of_mem_core
    (e.le_core (f.basis_mem_elementary n.t (by simp)))
  have hzv := f.commute_z_of_mem_core
    (e.le_core (f.basis_mem_elementary n.v (by simp)))
  have hzu := f.commute_z_of_mem_core
    (e.le_core (f.basis_mem_elementary f.u (by simp)))
  have zz : z*z=1 := by simpa only [pow_two] using hzs
  have shift {g : G} (hc : Commute z g) (r : G) : z*(g*r)=g*(z*r) := hc.left_comm r
  have hP (g : G) : P g = f.x⁻¹*g*f.x := by simp [P, R]
  simp only [← hP]
  change P f.b / (f.b*f.a) ∈ E ∧ P f.c / (f.c*f.a*f.b) ∈ E ∧
    P f.d / (f.d*f.a*f.b*f.c) ∈ E ∧ P (f.c*f.d) / f.d ∈ E
  refine ⟨step _ _ ?_, step _ _ ?_, step _ _ ?_, step _ _ ?_⟩
  all_goals
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [hz,ht,hv,hu,hw,R_mul,map_mul,az,at_,av,au,aw,bz,bt,bv,bu,bw,
        cz,ct,cv,cu,cw,dz,dt,dv,du,dw]
      all_goals simp only [mul_assoc, shift hzt, shift hzv, shift hzu, ← mul_assoc z z,
        zz, one_mul, mul_one, hzt.eq, hzv.eq, hzu.eq]
/-- Conjugation by a core element preserves the actual derived core. -/
public theorem derived_conjugate_mem {r g : G} (hr : r ∈ J) (hg : g ∈ E) :
    r⁻¹ * g * r ∈ E := by
  obtain ⟨rH, hrJ, rfl⟩ := hr
  obtain ⟨gJ, hgD, rfl⟩ := hg
  let rJ : pCore 2 H := ⟨rH, hrJ⟩
  have hc := (inferInstance : (commutator (pCore 2 H)).Normal).conj_mem
    gJ hgD rJ⁻¹
  simp only [inv_inv] at hc
  exact mem_map_of_mem ((H).subtype.comp (pCore 2 H).subtype) hc

/-- Equations (1)–(10) determine the three outer commutator cosets in J/E.
The proof compares the actions on E, whose centralizer is E itself. -/
public theorem outer_commutator_cosets [Finite G] (f : ParrottSylowInitialData n)
    (h : ParrottCentralizerHypotheses z) :
    Tits.parrottCommutator f.b f.x / f.a ∈ E ∧
    Tits.parrottCommutator f.c f.x / (f.a*f.b) ∈ E ∧
    Tits.parrottCommutator f.d f.x / (f.a*f.b*f.c) ∈ E := by
  obtain ⟨hb, hc, hd, _⟩ := f.outer_images_mod_derived h
  have step (g r : G) (hg : g ∈ J)
      (he : f.x⁻¹*g*f.x / (g*r) ∈ E) :
      Tits.parrottCommutator g f.x / r ∈ E := by
    have hh := derived_conjugate_mem hg he
    convert hh using 1
    simp only [Tits.parrottCommutator, div_eq_mul_inv]
    group
  exact ⟨step _ _ (f.generators_mem_core _ (by simp)) hb,
    step _ _ (f.generators_mem_core _ (by simp)) (by simpa only [mul_assoc] using hc),
    step _ _ (f.generators_mem_core _ (by simp)) (by simpa only [mul_assoc] using hd)⟩

/-- The four-by-four pairing of core and derived generators is already
antidiagonal before any of equations (11)–(15) has been selected. -/
public theorem core_derived_pairing_entries (f : ParrottSylowInitialData n) (i j : Fin 4) :
    Tits.parrottCommutator (![f.a,f.b,f.c,f.d] i) (![n.t,n.v,f.u,f.w] j) =
      z ^ (if i.val + j.val = 3 then 1 else 0) := by
  have ha (r : G) (hr : r ∈ ({n.t,n.v,f.u} : Set G)) :
      Tits.parrottCommutator f.a r = 1 := by
    apply (Tits.parrottCommutator_eq_one_iff _ _).mpr
    apply f.commute_of_mem_elementary (f.basis_mem_elementary _ (by simp))
    exact f.basis_mem_elementary r (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr ⊢
      tauto)
  have hat := ha n.t (by simp)
  have hav := ha n.v (by simp)
  have hau := ha f.u (by simp)
  have hbt := (Tits.parrottCommutator_eq_one_iff _ _).mpr f.comm_bt
  have hbv := (Tits.parrottCommutator_eq_one_iff _ _).mpr
    (show Commute f.b n.v by rw [← f.eq03_b]; exact Commute.self_pow _ _)
  have hdv := (Tits.parrottCommutator_eq_one_iff _ _).mpr f.core_commute_d_v
  fin_cases i <;> fin_cases j <;>
    simp [hat, hav, hau, hbt, hbv, hdv, f.eq02_aw, f.eq02_bu, f.eq02_bw,
      f.eq10_ct, f.eq10_cv, f.eq09_cu, f.eq09_cw, f.eq03_dt, f.eq08_du, f.eq07_dw]

/-- Squares of two core elements in the same derived coset differ only
by the marked central involution. -/
public theorem core_squares_eq_mod_center [Finite G]
    (h : ParrottCentralizerHypotheses z) {g k : G}
    (hg : g ∈ J) (hk : k ∈ J) (he : g / k ∈ E) :
    g ^ 2 / k ^ 2 ∈ zpowers z := by
  let K := pCore 2 H
  let D := commutator K
  let embed : K →* G := (H).subtype.comp K.subtype
  have hinj : Function.Injective embed := (H).subtype_injective.comp K.subtype_injective
  obtain ⟨gH, hgK, rfl⟩ := hg
  obtain ⟨kH, hkK, rfl⟩ := hk
  let a : K := ⟨gH, hgK⟩
  let b : K := ⟨kH, hkK⟩
  have hab : a / b ∈ D := by
    obtain ⟨v, hv, hev⟩ := he
    have hvab : v = a / b := hinj (by simpa only [map_div, embed, a, b, MonoidHom.comp_apply, Subgroup.subtype_apply, Subgroup.coe_mk] using hev)
    exact hvab ▸ hv
  obtain ⟨hZ, _, _, _, hUpper, hElem, _, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 D := hElem
  have hs := sq_eq_mod_center_of_eq_mod_elementary D hUpper.le a b
    (QuotientGroup.eq_iff_div_mem.mpr hab)
  have hz := mem_map_of_mem embed (QuotientGroup.eq_iff_div_mem.mp hs)
  rw [hZ] at hz
  simpa only [map_div, map_pow, embed, a, b, MonoidHom.comp_apply, Subgroup.subtype_apply, Subgroup.coe_mk] using hz

/-- The product of the supplied c and d has central square, without
changing c or assuming any of equations (11)–(15). -/
public theorem cd_square_central [Finite G] (f : ParrottSylowInitialData n)
    (h : ParrottCentralizerHypotheses z) : (f.c*f.d)^2 ∈ zpowers z := by
  have he := (f.outer_images_mod_derived h).2.2.2
  have hd := f.generators_mem_core f.d (by simp)
  have hEJ : E ≤ J := by
    rw [← map_map]
    exact map_mono (map_subtype_le _)
  have hg : f.x⁻¹*(f.c*f.d)*f.x ∈ J := by
    have hh := (J).mul_mem (hEJ he) hd
    simpa only [div_mul_cancel] using hh
  have hs := core_squares_eq_mod_center h hg hd he
  rw [f.d_sq, div_one] at hs
  have hxH : f.x ∈ H := e.sylow_le_centralizer
    (f.sylow_eq.symm ▸ mem_sup_left (mem_zpowers f.x))
  let Q : G →* G := (MulAut.conj f.x).toMonoidHom
  have hQz : Q z = z := by
    change f.x*z*f.x⁻¹=z
    rw [mem_centralizer_singleton_iff.mp hxH]
    simp
  have hQZ : (zpowers z).map Q = zpowers z := by
    rw [MonoidHom.map_zpowers, hQz]
  have hmap := mem_map_of_mem Q hs
  rw [hQZ, map_pow] at hmap
  simpa only [Q, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using hmap

/-- Commutators of actual core elements lie in the actual derived core. -/
public theorem core_commutator_mem_derived {g k : G} (hg : g ∈ J) (hk : k ∈ J) :
    Tits.parrottCommutator g k ∈ E := by
  obtain ⟨gH, hgK, rfl⟩ := hg
  obtain ⟨kH, hkK, rfl⟩ := hk
  let a : pCore 2 H := ⟨gH, hgK⟩
  let b : pCore 2 H := ⟨kH, hkK⟩
  have hh := commutator_mem_commutator (H₁ := (⊤ : Subgroup (pCore 2 H)))
    (H₂ := ⊤) (g₁ := a⁻¹) (g₂ := b⁻¹) (mem_top _) (mem_top _)
  have hm := mem_map_of_mem ((H).subtype.comp (pCore 2 H).subtype) hh
  simpa only [Tits.parrottCommutator, _root_.commutator_def, commutatorElement_def, map_mul, map_inv,
    inv_inv, a, b, MonoidHom.comp_apply, Subgroup.subtype_apply, Subgroup.coe_mk] using hm

/-- Every core square belongs to the actual derived core. -/
public theorem core_square_mem_derived [Finite G]
    (h : ParrottCentralizerHypotheses z) {g : G} (hg : g ∈ J) : g^2 ∈ E := by
  obtain ⟨gH, hgK, rfl⟩ := hg
  let a : pCore 2 H := ⟨gH, hgK⟩
  let D := commutator (pCore 2 H)
  let : IsElementaryAbelian 2 ((pCore 2 H) ⧸ D) :=
    (parrott_core_abelianization_structure z h).1
  have hs : (QuotientGroup.mk' D a)^2=1 := by
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 _) _
  rw [← map_pow] at hs
  exact mem_map_of_mem ((H).subtype.comp (pCore 2 H).subtype)
    ((QuotientGroup.eq_one_iff _).mp hs)

private theorem pc_commute_right {a b k : G}
    (hb : b^2=1) (hk : k^2=1) (he : Tits.parrottCommutator a b = k) :
    Commute b k := by
  have hb' : b⁻¹=b := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hb)
  have hk' : k⁻¹=k := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hk)
  have he' : Tits.parrottCommutator b a = k := by
    calc
      _ = (Tits.parrottCommutator a b)⁻¹ := by
        simp only [Tits.parrottCommutator]; group
      _ = k := by rw [he, hk']
  have heq : b*k = a⁻¹*b*a := by
    rw [← he']
    simp only [Tits.parrottCommutator]
    group
  have heq' := congrArg Inv.inv heq
  simp only [mul_inv_rev, hb', hk', inv_inv] at heq'
  exact heq.trans (by simpa only [mul_assoc] using heq'.symm)

/-- An elementary derived element has square one. -/
public theorem derived_square_one [Finite G]
    (h : ParrottCentralizerHypotheses z) {g : G} (hg : g ∈ E) : g^2=1 := by
  let : IsElementaryAbelian 2 (commutator (pCore 2 H)) :=
    (parrott_centralizer_structure z h).2.2.2.2.2.1
  let : IsElementaryAbelian 2 E :=
    IsElementaryAbelian.map ((H).subtype.comp (pCore 2 H).subtype)
  exact elemPow_eq_one_of_isElementaryAbelian _ hg

/-- The commutator of the initial a and d centralizes d. -/
public theorem commute_d_ad [Finite G] (f : ParrottSylowInitialData n)
    (h : ParrottCentralizerHypotheses z) : Commute f.d (Tits.parrottCommutator f.a f.d) :=
  pc_commute_right f.d_sq
    (derived_square_one h (core_commutator_mem_derived
      (f.generators_mem_core _ (by simp)) (f.generators_mem_core _ (by simp)))) rfl

/-- The initial c² centralizes d, since cd has central square. -/
public theorem commute_d_c_square [Finite G] (f : ParrottSylowInitialData n)
    (h : ParrottCentralizerHypotheses z) : Commute f.d (f.c^2) := by
  have hp : Commute f.d (Tits.parrottCommutator f.c f.d) :=
    pc_commute_right f.d_sq
      (derived_square_one h (core_commutator_mem_derived
        (f.generators_mem_core _ (by simp)) (f.generators_mem_core _ (by simp)))) rfl
  have hq : Commute f.d ((f.c*f.d)^2) := by
    have hd : Commute f.d z :=
      (f.commute_z_of_mem_core (f.generators_mem_core _ (by simp))).symm
    exact (mem_centralizer_singleton_iff.mp
      ((zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hd.symm.eq))
        (f.cd_square_central h))).symm
  have he : Tits.parrottCommutator f.c f.d = (f.c^2)⁻¹*(f.c*f.d)^2 := by
    have hd : f.d⁻¹=f.d := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using f.d_sq)
    simp only [Tits.parrottCommutator, hd, pow_two]
    group
  have hh := hp.mul_right hq.inv_right
  rw [he, mul_inv_cancel_right] at hh
  simpa only [inv_inv] using hh.inv_right

end Stellmacher.Recognition.ParrottSylowInitialData
