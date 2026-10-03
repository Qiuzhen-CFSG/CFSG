module

public import Stellmacher.Recognition.Parrott.SylowSeedOuterData
public import Stellmacher.Recognition.Parrott.SylowSeedMiddleNormalization
public import Stellmacher.Recognition.Parrott.SylowSeedLastRelations
public import Stellmacher.Recognition.Parrott.SylowSeedYcBound
public import Stellmacher.Recognition.Parrott.SylowSeedLastNormalization
public import Theory.SpecificGroups.Tits.RecognitionSylowFinalAdjustment

/-!
# Assembly after the last Sylow coordinate calculations

Once the middle and last outer relations are established on an actual seed,
all fields of the full generator frame follow. If [x,d] has a remaining
factor z, replacing x by xt removes it and preserves y=x²z, every earlier
relation, and all actual subgroup closures.

The initial centralization premises now give all the middle relations. The
square action determines [y,c], and a further residual coordinate choice
normalizes the last two outer images. The literal middle seed need not satisfy
(19), so the final theorem permits those auxiliary changes while preserving
the supplied marked elements and actual subgroups. The earlier conditional
assembly remains available as an interface for the separate calculations.

Source: Parrott (1972), §3, printed p.680, equations (16)–(19).
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSylowSeedData
variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

private theorem generators_of_exact_outer_relations (f : ParrottSylowSeedData n false)
    (hm : f.OuterMiddleRelations)
    (hyc : Tits.parrottCommutator (f.x^2*z) f.c = f.a*n.t*z)
    (hxc : Tits.parrottCommutator f.x f.c = f.a*f.b*f.u*n.v)
    (hxd : Tits.parrottCommutator f.x f.d = f.a*f.b*f.c*f.u*n.v) :
    Nonempty (ParrottSylowGeneratorData n) := by
  refine ⟨{
    u := f.u
    w := f.w
    a := f.a
    b := f.b
    c := f.c
    d := f.d
    x := f.x
    y := f.x^2*z
    derived_basis := f.derived_basis
    elementary_basis := f.elementary_basis
    core_generators := f.core_generators
    sylow_generators := f.sylow_generators
    z_sq := f.relations.z_sq
    t_sq := f.relations.t_sq
    v_sq := f.relations.v_sq
    u_sq := f.relations.u_sq
    w_sq := f.relations.w_sq
    a_sq := f.relations.a_sq
    comm_zt := f.relations.comm_zt
    comm_zv := f.relations.comm_zv
    comm_zu := f.relations.comm_zu
    comm_zw := f.relations.comm_zw
    comm_tv := f.relations.comm_tv
    comm_tu := f.relations.comm_tu
    comm_tw := f.relations.comm_tw
    comm_vu := f.relations.comm_vu
    comm_vw := f.relations.comm_vw
    comm_uw := f.relations.comm_uw
    comm_az := f.relations.comm_az
    comm_at := f.relations.comm_at
    comm_av := f.relations.comm_av
    comm_au := f.relations.comm_au
    comm_zb := f.relations.comm_zb
    comm_zc := f.relations.comm_zc
    comm_zd := f.relations.comm_zd
    comm_zx := f.relations.comm_zx
    comm_zy := f.relations.square_mul_z.2.2
    comm_bt := f.relations.comm_bt
    y_sq := f.relations.square_mul_z.1
    d_sq := f.relations.d_sq
    eq01_x := f.relations.eq01_x
    eq01_xt := f.relations.eq01_xt
    eq01_xv := f.relations.eq01_xv
    eq01_xu := f.relations.eq01_xu
    eq01_xw := f.relations.eq01_xw
    eq02_bw := f.relations.eq02_bw
    eq02_aw := f.relations.eq02_aw
    eq02_bu := f.relations.eq02_bu
    eq03_db := f.relations.eq03_db
    eq03_dt := f.relations.eq03_dt
    eq05_ab := f.relations.eq05_ab
    eq06_ya := f.relations.square_mul_z_comm_a
    eq07_dw := f.relations.eq07_dw
    eq08_du := f.relations.eq08_du
    eq09_cu := f.relations.eq09_cu
    eq09_cw := f.relations.eq09_cw
    eq10_ct := f.relations.eq10_ct
    eq10_cv := f.relations.eq10_cv
    eq11_ad := by simpa only [Bool.false_eq_true, ↓reduceIte] using f.relations.eq11_ad
    eq12_ac := by simpa only [Bool.false_eq_true, ↓reduceIte] using f.relations.eq12_ac
    eq14_cd := by simpa only [Bool.false_eq_true, ↓reduceIte] using f.relations.eq14_cd
    eq15_bc := by simpa only [Bool.false_eq_true, ↓reduceIte] using f.relations.eq15_bc
    eq16_ax := hm.eq16_ax
    eq17_yd := hm.eq17_yd
    eq18_bx := hm.eq18_bx
    eq18_by := (Tits.parrottCommutator_eq_one_iff _ _).mpr hm.comm_by
    eq19_yc := hyc
    eq19_xc := hxc
    eq19_xd := hxd
    eq03_b := f.relations.eq03_b
    eq04 := f.relations.square_mul_z.2.1
    eq13 := by simpa only [Bool.false_eq_true, ↓reduceIte] using f.relations.eq13
  }⟩

/-- Complete a full frame from (16)–(18) and (19) up to its final central error.
The possible correction retains z,t,v,F,T and every actual subgroup closure. -/
public theorem generators_of_outer_relations (f : ParrottSylowSeedData n false)
    (hm : f.OuterMiddleRelations) (hl : f.OuterLastRelations) :
    Nonempty (ParrottSylowGeneratorData n) := by
  rcases hl.eq19_xd with hd | hd
  · exact generators_of_exact_outer_relations f hm hl.eq19_yc hl.eq19_xc hd
  · let f' : ParrottSylowSeedData n false := {
      u := f.u
      w := f.w
      a := f.a
      b := f.b
      c := f.c
      d := f.d
      x := f.x*n.t
      derived_basis := f.derived_basis
      elementary_basis := f.elementary_basis
      core_generators := f.core_generators
      sylow_generators := f.relations.adjust_xt_sylow_closure.trans f.sylow_generators
      relations := f.relations.adjust_xt_relations }
    have hm' : f'.OuterMiddleRelations := {
      eq16_ax := f.relations.adjust_xt_ax hm.eq16_ax
      comm_by := by
        change Commute f.b ((f.x*n.t)^2*z)
        rw [f.relations.adjust_xt_square]
        exact hm.comm_by
      eq17_yd := by
        change Tits.parrottCommutator ((f.x*n.t)^2*z) f.d = f.b*f.w
        rw [f.relations.adjust_xt_square]
        exact hm.eq17_yd
      eq18_bx := f.relations.adjust_xt_bx hm.eq18_bx }
    apply generators_of_exact_outer_relations f' hm'
    · change Tits.parrottCommutator ((f.x*n.t)^2*z) f.c = f.a*n.t*z
      rw [f.relations.adjust_xt_square]
      exact hl.eq19_yc
    · exact f.relations.adjust_xt_xc hl.eq19_xc
    · exact f.relations.adjust_xt_xd hd

/-- Reduce completion to the two remaining last-stage calculations. The second
input may change auxiliary coordinates; requiring the last relations on every
literal middle seed would contradict its proved residual symmetry. The actual
marked data and subgroup closures remain fixed by the seed type. -/
public theorem exists_generators_of_b_comm_square_mul_z_of_last_steps
    [Finite G] [IsSimpleGroup G]
    (f : ParrottSylowSeedData n false)
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z)
    (hax : Tits.parrottCommutator f.a f.x = 1)
    (hby : Commute f.b (f.x^2*z))
    (hyc_cases : ∀ g : ParrottSylowSeedData n false, g.OuterMiddleRelations →
      Tits.parrottCommutator (g.x^2*z) g.c = g.a*n.t ∨
        Tits.parrottCommutator (g.x^2*z) g.c = g.a*n.t*z)
    (hnormalize : ∀ g : ParrottSylowSeedData n false, g.OuterMiddleRelations →
      Tits.parrottCommutator (g.x^2*z) g.c = g.a*n.t*z →
      ∃ g' : ParrottSylowSeedData n false,
        g'.OuterMiddleRelations ∧ g'.OuterLastRelations) :
    Nonempty (ParrottSylowGeneratorData n) := by
  obtain ⟨g, hm⟩ := f.exists_outer_middle_relations hns hN h hax hby
  have hyc := g.eq19_yc_of_alternative hns hN h hm (hyc_cases g hm)
  obtain ⟨g', hm', hl'⟩ := hnormalize g hm hyc
  exact g'.generators_of_outer_relations hm' hl'

/-- Complete equations (16)–(19) from the initial seed centralization inputs.
All coordinate choices retain z,t,v,F and the supplied Sylow subgroup literally. -/
public theorem exists_generators_of_b_comm_square_mul_z
    [Finite G] [IsSimpleGroup G]
    (f : ParrottSylowSeedData n false)
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z)
    (hax : Tits.parrottCommutator f.a f.x = 1)
    (hby : Commute f.b (f.x^2*z)) :
    Nonempty (ParrottSylowGeneratorData n) := by
  apply f.exists_generators_of_b_comm_square_mul_z_of_last_steps hns hN h hax hby
  · exact fun g hm => g.yc_cases h hm
  · exact fun g hm hyc => exists_outer_last_normalization hns hN h g hm hyc

end Stellmacher.Recognition.ParrottSylowSeedData
