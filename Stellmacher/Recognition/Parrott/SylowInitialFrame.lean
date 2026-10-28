module

public import Stellmacher.Recognition.Parrott.SylowSeedFrame

/-!
# Adapting a complete Sylow frame to the initial-frame interface

The lower local-generator interface already contains every equation through
(10), together with the first branch of the `a,x` alternative.  This adapter
retains the supplied `z,t,v,F,T` and exposes that data through
`ParrottSylowInitialData`.  The only geometric premise not stored by
`ParrottSylowGeneratorData` is the four-generator basis of `E ∩ F`; it is
therefore an explicit argument here.

This module deliberately does not claim an unconditional construction of the
core generators from `ParrottSylowActionData`.  Such a construction requires
the missing core-action selection argument from Parrott's pp.678–679 proof.
-/

open Subgroup
namespace Stellmacher.Recognition

variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

set_option quotPrecheck false in
local notation "H" => centralizer ({z} : Set G)
set_option quotPrecheck false in
local notation "J" => (pCore 2 H).map (H).subtype

/-- A complete local generator frame gives the initial frame once its
`E ∩ F` basis is supplied.  The actual subgroup equalities and every equation
through (10) are copied literally from the supplied frame. -/
public def ParrottSylowGeneratorData.toInitial
    (g : ParrottSylowGeneratorData n)
    (hinf : closure ({z, n.t, n.v, g.u} : Set G) =
      (commutator (pCore 2 H)).map ((H).subtype.comp (pCore 2 H).subtype) ⊓ e.F) :
    ParrottSylowInitialData n := by
  have hsyl : (e.sylow : Subgroup G) = zpowers g.x ⊔ J := by
    rw [← g.sylow_generators]
    rw [show ({g.x, g.a, g.b, g.c, g.d} : Set G) =
      {g.x} ∪ {g.a, g.b, g.c, g.d} by
      ext y
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union],
      Subgroup.closure_union, ← zpowers_eq_closure, g.core_generators]
  exact {
    u := g.u
    w := g.w
    x := g.x
    inf_basis := hinf
    derived_basis := g.derived_basis
    sylow_eq := hsyl
    eq01_x := g.eq01_x
    eq01_xt := g.eq01_xt
    eq01_xv := g.eq01_xv
    eq01_xu := g.eq01_xu
    eq01_xw := g.eq01_xw
    a := g.a
    b := g.b
    c := g.c
    d := g.d
    elementary_basis := g.elementary_basis
    core_generators := g.core_generators
    comm_bt := g.comm_bt
    d_sq := g.d_sq
    eq02_bw := g.eq02_bw
    eq02_aw := g.eq02_aw
    eq02_bu := g.eq02_bu
    eq03_db := g.eq03_db
    eq03_dt := g.eq03_dt
    eq03_b := g.eq03_b
    eq05_ab := g.eq05_ab
    eq07_dw := g.eq07_dw
    eq08_du := g.eq08_du
    eq09_cu := g.eq09_cu
    eq09_cw := g.eq09_cw
    eq10_ct := g.eq10_ct
    eq10_cv := g.eq10_cv
    ax_alternative := Or.inl g.eq16_ax }

end Stellmacher.Recognition
