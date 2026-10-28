module

public import Stellmacher.Recognition.Parrott.SylowSeedOuterData
public import Stellmacher.Recognition.Parrott.SylowSeedOuterGeometry
public import Theory.SpecificGroups.Tits.RecognitionSylowResidualSymmetry

/-!
# Residual coordinate ambiguity before Parrott's last Sylow equations

The literal intermediate seed still admits the simultaneous substitution
(a,b,c,d) ↦ (at,bv,cu,dw). It preserves its actual E,F,J,T, the marked
z,t,v, the outer generator x, the prescribed y=x²z, and (16)–(18).
It also preserves [y,c]=atz. However, if [x,c]=abuv before the substitution,
the new [x,c] differs from the new abuv by the nontrivial factor tz.

Consequently an exact [x,c]=abuv theorem cannot hold for every supplied
seed normalized only through (18), even after assuming [y,c]=atz.
The final coordinate construction needs a further normalization or a
stronger compatibility condition on its chosen core generators.

The proof uses word identities and closure equalities, rather than a
completed frame, a presentation, or an abstract replacement group.

Source: Parrott (1972), §3, printed pp.678–680, especially the paragraph
preceding (19). This module records the residual choice in translating
that paragraph to a statement about arbitrary literal seed data.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSylowSeedData
variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

/-- A residual change of the core coordinates, fixing every marked witness
and every actual subgroup of the supplied seed. -/
public def residual (f : ParrottSylowSeedData n false) : ParrottSylowSeedData n false where
  u := f.u
  w := f.w
  a := f.a*n.t
  b := f.b*n.v
  c := f.c*f.u
  d := f.d*f.w
  x := f.x
  derived_basis := f.derived_basis
  elementary_basis := Tits.ParrottSylowSeedRelations.residual_elementary_closure.trans
    f.elementary_basis
  core_generators := f.relations.residual_core_closure.trans f.core_generators
  sylow_generators := f.relations.residual_sylow_closure.trans f.sylow_generators
  relations := f.relations.residual_relations

/-- The residual substitution preserves all middle relations on the same y. -/
public theorem residual_middle (f : ParrottSylowSeedData n false)
    (hm : f.OuterMiddleRelations) : f.residual.OuterMiddleRelations where
  eq16_ax := f.relations.residual_ax hm.eq16_ax
  comm_by := f.relations.residual_by hm.comm_by
  eq17_yd := f.relations.residual_yd hm.eq17_yd
  eq18_bx := f.relations.residual_bx hm.eq18_bx

/-- Selection of the central factor in [y,c] does not remove the residual choice. -/
public theorem residual_yc (f : ParrottSylowSeedData n false)
    (hc : Tits.parrottCommutator (f.x^2*z) f.c = f.a*n.t*z) :
    Tits.parrottCommutator (f.residual.x^2*z) f.residual.c =
      f.residual.a*n.t*z :=
  f.relations.residual_yc hc

/-- The residual substitution changes the proposed last c-commutator by tz. -/
public theorem residual_xc (f : ParrottSylowSeedData n false)
    (hc : Tits.parrottCommutator f.x f.c = f.a*f.b*f.u*n.v) :
    Tits.parrottCommutator f.residual.x f.residual.c =
      (f.residual.a*f.residual.b*f.residual.u*n.v)*(n.t*z) :=
  f.relations.residual_xc hc

/-- The marked independence of t and z makes this discrepancy nontrivial. -/
public theorem residual_xc_ne (f : ParrottSylowSeedData n false)
    (hc : Tits.parrottCommutator f.x f.c = f.a*f.b*f.u*n.v) :
    Tits.parrottCommutator f.residual.x f.residual.c ≠
      f.residual.a*f.residual.b*f.residual.u*n.v := by
  rw [f.residual_xc hc]
  intro he
  have htz : n.t*z=1 := mul_left_cancel (he.trans (mul_one _).symm)
  apply n.t_not_mem_zpowers
  have ht : n.t=z⁻¹ := eq_inv_of_mul_eq_one_left htz
  rw [ht]
  exact inv_mem (mem_zpowers z)

/-- Any seed satisfying the selected y-equation yields a seed satisfying the
same premises but failing the proposed exact x,c equation. In particular the
latter cannot be a universal consequence for a literal intermediate seed.
All original ambient hypotheses and marked witnesses can be retained. -/
public theorem exists_seed_not_eq19_xc (f : ParrottSylowSeedData n false)
    (hm : f.OuterMiddleRelations)
    (hc : Tits.parrottCommutator (f.x^2*z) f.c = f.a*n.t*z) :
    ∃ f' : ParrottSylowSeedData n false,
      f'.OuterMiddleRelations ∧
      Tits.parrottCommutator (f'.x^2*z) f'.c = f'.a*n.t*z ∧
      Tits.parrottCommutator f'.x f'.c ≠ f'.a*f'.b*f'.u*n.v := by
  by_cases hx : Tits.parrottCommutator f.x f.c = f.a*f.b*f.u*n.v
  · exact ⟨f.residual, f.residual_middle hm, f.residual_yc hc, f.residual_xc_ne hx⟩
  · exact ⟨f, hm, hc, hx⟩

end Stellmacher.Recognition.ParrottSylowSeedData
