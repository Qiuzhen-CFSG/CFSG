module

public import Stellmacher.Recognition.Parrott.SylowSeedData
public import Theory.SpecificGroups.Tits.RecognitionSylowOuterAdjustment

/-!
# The first outer-generator normalization in Parrott's Sylow construction

The unprimed seed has [a,x] equal to 1 or t. In the second case, replace a
by av and c by cw. The word identities preserve every seed relation and
all four actual subgroup closures, and give [av,x]=1. Thus the remaining
outer-generator construction may start with equation (16), retaining the
supplied z,t,v,F,T literally. This module does not yet assert the existence
of the full frame: the remaining local-action and coordinate calculations
must establish equations (17)–(19).

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§3, printed p.680, equation (16) and its following substitution.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSylowSeedData
variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e}

/-- Equation (16) can be imposed while preserving the original local subgroups
and the marked elements z,t,v. Only the auxiliary a,c coordinates change. -/
public theorem exists_ax_eq_one (f : ParrottSylowSeedData n false) :
    ∃ f' : ParrottSylowSeedData n false,
      Tits.parrottCommutator f'.a f'.x = 1 := by
  rcases f.relations.ax_alternative with ha | ha
  · exact ⟨f, ha⟩
  · let f' : ParrottSylowSeedData n false := {
      u := f.u
      w := f.w
      a := f.a*n.v
      b := f.b
      c := f.c*f.w
      d := f.d
      x := f.x
      derived_basis := f.derived_basis
      elementary_basis := Tits.ParrottSylowSeedRelations.adjust_ax_elementary_closure.trans
        f.elementary_basis
      core_generators := (f.relations.adjust_ax_core_closure ha).trans f.core_generators
      sylow_generators := (f.relations.adjust_ax_sylow_closure ha).trans f.sylow_generators
      relations := f.relations.adjust_ax_relations ha }
    exact ⟨f', f.relations.adjust_ax_eq ha⟩

end Stellmacher.Recognition.ParrottSylowSeedData
