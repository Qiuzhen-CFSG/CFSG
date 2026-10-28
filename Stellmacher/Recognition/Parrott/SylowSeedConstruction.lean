module

public import Stellmacher.Recognition.Parrott.SylowSeedData
public import Stellmacher.Recognition.Parrott.SylowSeedFrame
public import Stellmacher.Recognition.Parrott.SylowCoreCaseChoice
public import Stellmacher.Recognition.Parrott.SylowABGeometry
public import Stellmacher.Recognition.Parrott.SylowFourthGeneratorSelection
public import Stellmacher.Recognition.Parrott.SylowBWAlignment

/-!
# Assembly of the actual Sylow seed

An initial frame through (10), together with either set of core equations
(11)–(15), gives the seed on the supplied E,F,J,T. All elementary equations
are proved from membership in E and F, centrality of z comes from the actual
centralizer, and the Sylow generation equality follows from T = ⟨x,J⟩.

The proved core-choice theorem supplies the remaining equations (11)–(15)
from any initial frame. The action-frame construction and quadratic alignment
supply a frame with [n.b,w]=1. Three-generator selection, fourth-generator
completion and core-case choice then prove seed existence from the supplied
normalizer data, preserving z,t,v and the actual E,F,J,T.

Source: Parrott (1972), §3, printed pp.678–679.
-/

open Subgroup
open scoped IsMulCommutative
namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

namespace ParrottSylowInitialData

/-- Assemble a seed after the geometric construction and the five core choices.
In particular, the elementary and centrality equations are discharged from
actual subgroup information, rather than required as additional inputs. -/
public def toSeed [Finite G] (f : ParrottSylowInitialData n)
    (h : ParrottCentralizerHypotheses z) {caseTwo : Bool}
    (hc : CoreRelations f caseTwo) : ParrottSylowSeedData n caseTwo := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsElementaryAbelian 2 (commutator J) :=
    (parrott_centralizer_structure z h).2.2.2.2.2.1
  letI : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  letI : IsElementaryAbelian 2 e.F := e.elementary
  have hzE : z ∈ E := e.z_mem_inf.1
  have htE : n.t ∈ E := n.t_mem_inf.1
  have hvE : n.v ∈ E := n.v_mem_inf.1
  have huE : f.u ∈ E := by
    dsimp only [E, J, H]
    rw [← f.derived_basis]
    exact subset_closure (by simp)
  have hwE : f.w ∈ E := by
    dsimp only [E, J, H]
    rw [← f.derived_basis]
    exact subset_closure (by simp)
  have haF : f.a ∈ e.F := by
    rw [← f.elementary_basis]
    exact subset_closure (by simp)
  have huF : f.u ∈ e.F := by
    rw [← f.elementary_basis]
    exact subset_closure (by simp)
  have commE {r s : G} (hr : r ∈ E) (hs : s ∈ E) : Commute r s :=
    setLike_mul_comm hr hs
  have commF {r s : G} (hr : r ∈ e.F) (hs : s ∈ e.F) : Commute r s :=
    setLike_mul_comm hr hs
  have hgen : ∀ g ∈ ({f.a, f.b, f.c, f.d} : Set G), g ∈ J.map H.subtype := by
    intro g hg
    rw [← f.core_generators]
    exact subset_closure hg
  have hzgen : ∀ g ∈ ({f.a, f.b, f.c, f.d} : Set G), Commute z g := by
    intro g hg
    exact (mem_centralizer_singleton_iff.mp (map_subtype_le J (hgen g hg))).symm
  have hxT : f.x ∈ (e.sylow : Subgroup G) := by
    rw [f.sylow_eq]
    exact mem_sup_left (mem_zpowers f.x)
  have hTH : (e.sylow : Subgroup G) ≤ H := by
    rw [e.sylow_map]
    exact map_subtype_le _
  refine {
    u := f.u
    w := f.w
    a := f.a
    b := f.b
    c := f.c
    d := f.d
    x := f.x
    derived_basis := f.derived_basis
    elementary_basis := f.elementary_basis
    core_generators := f.core_generators
    sylow_generators := ?_
    relations := {
      z_sq := elemPow_eq_one_of_isElementaryAbelian z hzE
      t_sq := elemPow_eq_one_of_isElementaryAbelian n.t htE
      v_sq := elemPow_eq_one_of_isElementaryAbelian n.v hvE
      u_sq := elemPow_eq_one_of_isElementaryAbelian f.u huE
      w_sq := elemPow_eq_one_of_isElementaryAbelian f.w hwE
      a_sq := elemPow_eq_one_of_isElementaryAbelian f.a haF
      comm_zt := commE hzE htE
      comm_zv := commE hzE hvE
      comm_zu := commE hzE huE
      comm_zw := commE hzE hwE
      comm_tv := commE htE hvE
      comm_tu := commE htE huE
      comm_tw := commE htE hwE
      comm_vu := commE hvE huE
      comm_vw := commE hvE hwE
      comm_uw := commE huE hwE
      comm_az := commF haF e.z_mem_inf.2
      comm_at := commF haF n.t_mem_inf.2
      comm_av := commF haF n.v_mem_inf.2
      comm_au := commF haF huF
      comm_zb := hzgen f.b (by simp)
      comm_zc := hzgen f.c (by simp)
      comm_zd := hzgen f.d (by simp)
      comm_zx := (mem_centralizer_singleton_iff.mp (hTH hxT)).symm
      comm_bt := f.comm_bt
      d_sq := f.d_sq
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
      eq07_dw := f.eq07_dw
      eq08_du := f.eq08_du
      eq09_cu := f.eq09_cu
      eq09_cw := f.eq09_cw
      eq10_ct := f.eq10_ct
      eq10_cv := f.eq10_cv
      eq11_ad := hc.eq11_ad
      eq12_ac := hc.eq12_ac
      eq14_cd := hc.eq14_cd
      eq15_bc := hc.eq15_bc
      eq03_b := f.eq03_b
      eq13 := hc.eq13
      ax_alternative := f.ax_alternative } }
  rw [show ({f.x, f.a, f.b, f.c, f.d} : Set G) =
    {f.x} ∪ {f.a, f.b, f.c, f.d} from rfl,
    Subgroup.closure_union, ← zpowers_eq_closure, f.core_generators, ← f.sylow_eq]

/-- Every actual initial frame extends, after the proved core choices, to a
seed satisfying either printed case of (11)–(15). -/
public theorem exists_seed [Finite G] [IsSimpleGroup G]
    (f : ParrottSylowInitialData n) (hns : ¬ Group.IsSolvable G)
    (hN : IsNTwoGroup G) (h : ParrottCentralizerHypotheses z) :
    ∃ caseTwo : Bool, Nonempty (ParrottSylowSeedData n caseTwo) := by
  obtain ⟨caseTwo, f', hc⟩ := f.exists_core_case hns hN h
  exact ⟨caseTwo, ⟨f'.toSeed h hc⟩⟩

end ParrottSylowInitialData

/-- Complete the seed from an action frame whose w commutes with the supplied
three-centralizer generator. All other generator choices are discharged. -/
public theorem ParrottSylowActionData.exists_seed_of_commutator_bw
    [Finite G] [IsSimpleGroup G]
    (f : ParrottSylowActionData n) (hns : ¬ Group.IsSolvable G)
    (hN : IsNTwoGroup G) (h : ParrottCentralizerHypotheses z)
    (hbw : Tits.parrottCommutator n.b f.w = 1) :
    ∃ caseTwo : Bool, Nonempty (ParrottSylowSeedData n caseTwo) := by
  obtain ⟨g⟩ := f.exists_three_generators_of_commutator_bw hns hN h hbw
  obtain ⟨i⟩ := g.exists_initial h
  exact i.exists_seed hns hN h

/-- The supplied normalizer data admit actual Sylow seed generators satisfying
either printed case of equations (1)–(15), with z,t,v and E,F,J,T preserved. -/
public theorem ParrottNormalizerFusionData.exists_sylow_seed
    [Finite G] [IsSimpleGroup G]
    (n : ParrottNormalizerFusionData e) (hns : ¬ Group.IsSolvable G)
    (hN : IsNTwoGroup G) (h : ParrottCentralizerHypotheses z) :
    ∃ caseTwo : Bool, Nonempty (ParrottSylowSeedData n caseTwo) := by
  obtain ⟨f, hbw⟩ := n.exists_sylow_action_commutator_bw h hN
  exact f.exists_seed_of_commutator_bw hns hN h hbw

end Stellmacher.Recognition
