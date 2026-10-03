module

public import Stellmacher.Recognition.Parrott.NormalizerFusion
public import Theory.SpecificGroups.Tits.RecognitionLocalData

/-!
# Compatible witnesses for Parrott's local generators

The construction in §3 first normalizes generators of the actual Sylow subgroup
T, then extends them to the centralizer H and normalizer N. These interfaces
separate those proofs
while retaining the supplied second elementary subgroup F and fusion witnesses
z,t,v. The equations are exactly the unprimed source equations (1)–(26).

The closure equalities for E and F, together with their already proved elementary
structure and orders 32, express elementary bases. The other equalities retain
the actual subgroups J,T,H,N, rather than abstract groups of the same orders.
This module does not assert existence of the frames. The recognition owner
must construct both from the original hypotheses.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§3, pp.678–682. The changes from (11′)–(15′) and (23′) must be discharged
in the centralizer construction; they are not simultaneous input relations.
-/

open Subgroup

namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z}

/-- A normalized Sylow frame satisfying equations (1)–(19). The original
F,T,t,v are retained literally. The auxiliary a,b may change during normalization. -/
public structure ParrottSylowGeneratorData (n : ParrottNormalizerFusionData e) where
  u : G
  w : G
  a : G
  b : G
  c : G
  d : G
  x : G
  y : G
  derived_basis : closure ({z, n.t, n.v, u, w} : Set G) =
    (commutator (pCore 2 (centralizer ({z} : Set G)))).map
      ((centralizer ({z} : Set G)).subtype.comp
        (pCore 2 (centralizer ({z} : Set G))).subtype)
  elementary_basis : closure ({z, n.t, n.v, u, a} : Set G) = e.F
  core_generators : closure ({a, b, c, d} : Set G) =
    (pCore 2 (centralizer ({z} : Set G))).map (centralizer ({z} : Set G)).subtype
  sylow_generators : closure ({x, a, b, c, d} : Set G) = (e.sylow : Subgroup G)
  z_sq : z ^ 2 = 1
  t_sq : n.t ^ 2 = 1
  v_sq : n.v ^ 2 = 1
  u_sq : u ^ 2 = 1
  w_sq : w ^ 2 = 1
  a_sq : a ^ 2 = 1
  comm_zt : Commute z n.t
  comm_zv : Commute z n.v
  comm_zu : Commute z u
  comm_zw : Commute z w
  comm_tv : Commute n.t n.v
  comm_tu : Commute n.t u
  comm_tw : Commute n.t w
  comm_vu : Commute n.v u
  comm_vw : Commute n.v w
  comm_uw : Commute u w
  comm_az : Commute a z
  comm_at : Commute a n.t
  comm_av : Commute a n.v
  comm_au : Commute a u
  comm_zb : Commute z b
  comm_zc : Commute z c
  comm_zd : Commute z d
  comm_zx : Commute z x
  comm_zy : Commute z y
  comm_bt : Commute b n.t
  y_sq : y ^ 2 = 1
  d_sq : d ^ 2 = 1
  eq01_x : x ^ 4 = 1
  eq01_xt : Tits.parrottCommutator x n.t = 1
  eq01_xv : Tits.parrottCommutator x n.v = n.t
  eq01_xu : Tits.parrottCommutator x u = n.v
  eq01_xw : Tits.parrottCommutator x w = u
  eq02_bw : Tits.parrottCommutator b w = 1
  eq02_aw : Tits.parrottCommutator a w = z
  eq02_bu : Tits.parrottCommutator b u = z
  eq03_db : Tits.parrottCommutator d b = n.v
  eq03_dt : Tits.parrottCommutator d n.t = z
  eq05_ab : Tits.parrottCommutator a b = n.t
  eq06_ya : Tits.parrottCommutator y a = 1
  eq07_dw : Tits.parrottCommutator d w = 1
  eq08_du : Tits.parrottCommutator d u = 1
  eq09_cu : Tits.parrottCommutator c u = 1
  eq09_cw : Tits.parrottCommutator c w = 1
  eq10_ct : Tits.parrottCommutator c n.t = 1
  eq10_cv : Tits.parrottCommutator c n.v = z
  eq11_ad : Tits.parrottCommutator a d = u
  eq12_ac : Tits.parrottCommutator a c = n.v * n.t
  eq14_cd : Tits.parrottCommutator c d = w * u
  eq15_bc : Tits.parrottCommutator b c = u * n.v
  eq16_ax : Tits.parrottCommutator a x = 1
  eq17_yd : Tits.parrottCommutator y d = b * w
  eq18_bx : Tits.parrottCommutator b x = a
  eq18_by : Tits.parrottCommutator b y = 1
  eq19_yc : Tits.parrottCommutator y c = a * n.t * z
  eq19_xc : Tits.parrottCommutator x c = a * b * u * n.v
  eq19_xd : Tits.parrottCommutator x d = a * b * c * u * n.v
  eq03_b : b ^ 2 = n.v
  eq04 : x ^ 2 = y * z
  eq13 : c ^ 2 = w * u

/-- A centralizer frame with equations (20)–(24), on normalized Sylow
coordinates. Constructing this frame may require replacing the supplied Sylow
coordinates to handle the alternatives on pp.680–681, while retaining F,T,t,v. -/
public structure ParrottCentralizerGeneratorData (n : ParrottNormalizerFusionData e)
    extends ParrottSylowGeneratorData n where
  r : G
  centralizer_generators : (e.sylow : Subgroup G) ⊔ zpowers r = centralizer ({z} : Set G)
  r_order : orderOf r = 2
  r_conjugate : IsConj r z
  comm_zr : Commute z r
  eq20_r : r ^ 2 = 1
  eq20_ry : (r * y) ^ 5 = 1
  eq20_tr : r⁻¹ * n.t * r = w * u * n.v * z
  eq21_vr : r⁻¹ * n.v * r = u * n.v
  eq22_ur : r⁻¹ * u * r = u
  eq22_wr : r⁻¹ * w * r = n.v * n.t * z
  eq23_ar : r⁻¹ * a * r = d * u
  eq23_dr : r⁻¹ * d * r = a * u
  eq23_cr : r⁻¹ * c * r = c * d * a * u
  eq23_br : r⁻¹ * b * r = d * c * b * n.v * n.t
  eq24 : r * x * r = (y * r) ^ 2 * x

/-- The remaining generator and source equations for the actual normalizer,
on a supplied normalized centralizer frame. No braid equation is included. -/
public structure ParrottNormalizerGeneratorData {n : ParrottNormalizerFusionData e}
    (f : ParrottCentralizerGeneratorData n) where
  s : G
  normalizer_generators : (e.sylow : Subgroup G) ⊔ zpowers s = normalizer (e.F : Set G)
  s_order : orderOf s = 2
  s_conjugate : IsConj s n.v
  s_sq : s ^ 2 = 1
  eq25_ts : s⁻¹ * n.t * s = z
  eq25_vs : s⁻¹ * n.v * s = n.v * n.t * z
  eq25_ys : s⁻¹ * f.y * s = f.w * f.u * n.v * z
  eq25_ws : s⁻¹ * f.w * s = f.y * f.a * n.v * z
  eq25_as : s⁻¹ * f.a * s = f.u
  eq25_bs : s⁻¹ * f.b * s = f.b * f.a * f.u * n.v * z
  eq25_cs : s⁻¹ * f.c * s = f.x * f.y * f.a * f.u * n.v * n.t
  eq25_xs : s⁻¹ * f.x * s = f.c * f.a * f.w * n.t * z
  eq26 : (s * f.d * n.v * z) ^ 3 = 1

variable {n : ParrottNormalizerFusionData e}

namespace ParrottSylowGeneratorData

variable (f : ParrottSylowGeneratorData n)

/-- All eleven generators preceding r and s belong to the actual Sylow
subgroup. In particular, the equation x²=yz determines y inside that subgroup. -/
public theorem local_mem_sylow :
    z ∈ e.sylow ∧ n.t ∈ e.sylow ∧ n.v ∈ e.sylow ∧
      f.u ∈ e.sylow ∧ f.w ∈ e.sylow ∧ f.a ∈ e.sylow ∧ f.b ∈ e.sylow ∧
      f.c ∈ e.sylow ∧ f.d ∈ e.sylow ∧ f.x ∈ e.sylow ∧ f.y ∈ e.sylow := by
  have hgen : ∀ g ∈ ({f.x, f.a, f.b, f.c, f.d} : Set G), g ∈ e.sylow := by
    intro g hg
    change g ∈ (e.sylow : Subgroup G)
    rw [← f.sylow_generators]
    exact subset_closure hg
  have hx := hgen f.x (by simp)
  have ha := hgen f.a (by simp)
  have hb := hgen f.b (by simp)
  have hc := hgen f.c (by simp)
  have hd := hgen f.d (by simp)
  have hz := e.le_sylow e.z_mem_inf.2
  have ht := e.le_sylow n.t_mem_inf.2
  have hv := e.le_sylow n.v_mem_inf.2
  have hu : f.u ∈ e.sylow := by
    apply e.le_sylow
    rw [← f.elementary_basis]
    exact subset_closure (by simp)
  have hw : f.w ∈ e.sylow := by
    have hwu := (e.sylow : Subgroup G).pow_mem hc 2
    rw [f.eq13] at hwu
    exact ((e.sylow : Subgroup G).mul_mem_cancel_right hu).mp hwu
  have hy : f.y ∈ e.sylow := by
    have hyz := (e.sylow : Subgroup G).pow_mem hx 2
    rw [f.eq04] at hyz
    exact ((e.sylow : Subgroup G).mul_mem_cancel_right hz).mp hyz
  exact ⟨hz, ht, hv, hu, hw, ha, hb, hc, hd, hx, hy⟩

end ParrottSylowGeneratorData

namespace ParrottCentralizerGeneratorData

variable (f : ParrottCentralizerGeneratorData n)

/-- The centralizer generator is in the supplied centralizer. -/
public theorem r_mem_centralizer : f.r ∈ centralizer ({z} : Set G) := by
  rw [← f.centralizer_generators]
  exact mem_sup_right (mem_zpowers f.r)

end ParrottCentralizerGeneratorData

namespace ParrottNormalizerGeneratorData

variable {n : ParrottNormalizerFusionData e} {f : ParrottCentralizerGeneratorData n}

/-- Assemble the two construction interfaces into the already proved local
word-algebra interface. This is an adapter, not a witness-existence theorem. -/
public theorem localRelations (k : ParrottNormalizerGeneratorData f) :
    Tits.ParrottLocalRelations z n.t n.v f.u f.w f.a f.b f.c f.d f.x f.y f.r k.s where
  z_sq := f.z_sq
  t_sq := f.t_sq
  v_sq := f.v_sq
  u_sq := f.u_sq
  w_sq := f.w_sq
  a_sq := f.a_sq
  comm_zt := f.comm_zt
  comm_zv := f.comm_zv
  comm_zu := f.comm_zu
  comm_zw := f.comm_zw
  comm_tv := f.comm_tv
  comm_tu := f.comm_tu
  comm_tw := f.comm_tw
  comm_vu := f.comm_vu
  comm_vw := f.comm_vw
  comm_uw := f.comm_uw
  comm_az := f.comm_az
  comm_at := f.comm_at
  comm_av := f.comm_av
  comm_au := f.comm_au
  comm_zb := f.comm_zb
  comm_zc := f.comm_zc
  comm_zd := f.comm_zd
  comm_zx := f.comm_zx
  comm_zy := f.comm_zy
  comm_bt := f.comm_bt
  y_sq := f.y_sq
  d_sq := f.d_sq
  s_sq := k.s_sq
  eq01_x := f.eq01_x
  eq01_xt := f.eq01_xt
  eq01_xv := f.eq01_xv
  eq01_xu := f.eq01_xu
  eq01_xw := f.eq01_xw
  eq02_bw := f.eq02_bw
  eq02_aw := f.eq02_aw
  eq02_bu := f.eq02_bu
  eq03_db := f.eq03_db
  eq03_dt := f.eq03_dt
  eq05_ab := f.eq05_ab
  eq06_ya := f.eq06_ya
  eq07_dw := f.eq07_dw
  eq08_du := f.eq08_du
  eq09_cu := f.eq09_cu
  eq09_cw := f.eq09_cw
  eq10_ct := f.eq10_ct
  eq10_cv := f.eq10_cv
  eq11_ad := f.eq11_ad
  eq12_ac := f.eq12_ac
  eq14_cd := f.eq14_cd
  eq15_bc := f.eq15_bc
  eq16_ax := f.eq16_ax
  eq17_yd := f.eq17_yd
  eq18_bx := f.eq18_bx
  eq18_by := f.eq18_by
  eq19_yc := f.eq19_yc
  eq19_xc := f.eq19_xc
  eq19_xd := f.eq19_xd
  eq03_b := f.eq03_b
  eq04 := f.eq04
  eq13 := f.eq13
  eq25_ts := k.eq25_ts
  eq25_vs := k.eq25_vs
  eq25_ys := k.eq25_ys
  eq25_ws := k.eq25_ws
  eq25_as := k.eq25_as
  eq25_bs := k.eq25_bs
  eq25_cs := k.eq25_cs
  eq25_xs := k.eq25_xs
  eq26 := k.eq26
  comm_zr := f.comm_zr
  eq20_r := f.eq20_r
  eq20_ry := f.eq20_ry
  eq20_tr := f.eq20_tr
  eq21_vr := f.eq21_vr
  eq22_ur := f.eq22_ur
  eq22_wr := f.eq22_wr
  eq23_ar := f.eq23_ar
  eq23_dr := f.eq23_dr
  eq23_cr := f.eq23_cr
  eq23_br := f.eq23_br
  eq24 := f.eq24

end ParrottNormalizerGeneratorData

end Stellmacher.Recognition
