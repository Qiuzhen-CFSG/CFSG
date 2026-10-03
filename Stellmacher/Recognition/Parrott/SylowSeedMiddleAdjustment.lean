module

public import Stellmacher.Recognition.Parrott.SylowSeedOuterData
public import Theory.SpecificGroups.Tits.RecognitionSylowMiddleAdjustment

/-!
# Coordinate corrections on actual Sylow seeds

Explicit coordinate changes retain the marked z,t,v and all four actual
subgroup closures. Once [x²z,d] is known to be in bw⟨v,z⟩, changing x to xv
removes its z-error, and changing a to at and d to dw removes its v-error.
The resulting seed satisfies (16), (17), and Commute b (x²z).

The existence of the initial commutator-coset bound and the subsequent
normalization of (18) are separate mathematical inputs still to be proved.
No existence assertion for the full middle relations is made here yet.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§3, printed p.680, equations (16)–(18).
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSylowSeedData
variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

/-- The replacement x↦xv, in the same actual local subgroups. -/
@[expose] public def adjustXv (f : ParrottSylowSeedData n false) :
    ParrottSylowSeedData n false :=
  { f with
    x := f.x*n.v
    sylow_generators := f.relations.adjust_xv_sylow_closure.trans f.sylow_generators
    relations := f.relations.adjust_xv_relations }

/-- The replacement x↦xu, in the same actual local subgroups. -/
@[expose] public def adjustXu (f : ParrottSylowSeedData n false) :
    ParrottSylowSeedData n false :=
  { f with
    x := f.x*f.u
    sylow_generators := f.relations.adjust_xu_sylow_closure.trans f.sylow_generators
    relations := f.relations.adjust_xu_relations }

/-- The simultaneous replacement a↦at, d↦dw preserves F, the core, and T. -/
@[expose] public def adjustDw (f : ParrottSylowSeedData n false)
    (hax : Tits.parrottCommutator f.a f.x = 1) : ParrottSylowSeedData n false :=
  { f with
    a := f.a*n.t
    d := f.d*f.w
    elementary_basis := Tits.ParrottSylowSeedRelations.adjust_dw_elementary_closure.trans
      f.elementary_basis
    core_generators := (f.relations.adjust_dw_core_closure hax).trans f.core_generators
    sylow_generators := (f.relations.adjust_dw_sylow_closure hax).trans f.sylow_generators
    relations := f.relations.adjust_dw_relations hax }

/-- Once the four possibilities for [y,d] have been established, actual
coordinate corrections give (17), retaining (16) and the centralization of b. -/
public theorem exists_eq17_of_yd_cases (f : ParrottSylowSeedData n false)
    (hax : Tits.parrottCommutator f.a f.x = 1) (hby : Commute f.b (f.x^2*z))
    (hyd : Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w ∨
      Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w*z ∨
      Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w*n.v ∨
      Tits.parrottCommutator (f.x^2*z) f.d = f.b*f.w*n.v*z) :
    ∃ f' : ParrottSylowSeedData n false,
      Tits.parrottCommutator f'.a f'.x = 1 ∧ Commute f'.b (f'.x^2*z) ∧
      Tits.parrottCommutator (f'.x^2*z) f'.d = f'.b*f'.w := by
  have finish (g : ParrottSylowSeedData n false)
      (ha : Tits.parrottCommutator g.a g.x = 1) (hb : Commute g.b (g.x^2*z))
      (hd : Tits.parrottCommutator (g.x^2*z) g.d = g.b*g.w ∨
        Tits.parrottCommutator (g.x^2*z) g.d = g.b*g.w*n.v) :
      ∃ g' : ParrottSylowSeedData n false,
        Tits.parrottCommutator g'.a g'.x = 1 ∧ Commute g'.b (g'.x^2*z) ∧
        Tits.parrottCommutator (g'.x^2*z) g'.d = g'.b*g'.w := by
    rcases hd with hd | hd
    · exact ⟨g, ha, hb, hd⟩
    · refine ⟨g.adjustDw ha, g.relations.adjust_dw_ax ha, hb, ?_⟩
      have hwb := ((Tits.parrottCommutator_eq_one_iff _ _).mp g.relations.eq02_bw).symm
      have hvb : Commute n.v g.b :=
        (g.relations.eq03_b ▸ Commute.self_pow g.b 2).symm
      have he := g.relations.adjust_dw_yd hd
        ((hwb.mul_right (Commute.refl g.w)).mul_right g.relations.comm_vw.symm)
        ((hvb.mul_right g.relations.comm_vw).mul_right (Commute.refl n.v))
      simpa only [adjustDw, mul_assoc, ← pow_two, g.relations.v_sq, mul_one] using he
  have htbw : Commute n.t (f.b*f.w) := f.relations.comm_bt.symm.mul_right f.relations.comm_tw
  rcases hyd with hd | hd | hd | hd
  · exact finish f hax hby (Or.inl hd)
  · apply finish f.adjustXv (f.relations.adjust_xv_ax hax) (f.relations.adjust_xv_by hby)
    left
    have he := f.relations.adjust_xv_yd hd (htbw.mul_right f.relations.comm_zt.symm)
    simpa only [adjustXv, mul_assoc, ← pow_two, f.relations.z_sq, mul_one] using he
  · exact finish f hax hby (Or.inr hd)
  · apply finish f.adjustXv (f.relations.adjust_xv_ax hax) (f.relations.adjust_xv_by hby)
    right
    have he := f.relations.adjust_xv_yd hd
      ((htbw.mul_right f.relations.comm_tv).mul_right f.relations.comm_zt.symm)
    simpa only [adjustXv, mul_assoc, ← pow_two, f.relations.z_sq, mul_one] using he

end Stellmacher.Recognition.ParrottSylowSeedData
