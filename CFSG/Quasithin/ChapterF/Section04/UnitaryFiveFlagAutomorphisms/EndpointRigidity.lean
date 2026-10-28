module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveFlagAutomorphisms.TorusNormalization
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.EndpointRigidity
public import CFSG.Quasithin.Chapter5.Section03UnitaryNativeLift.Models

/-!
# The whole plane residual detects the native U₅ flag actor

Its intersection with the opposite endpoint contains the full line radical.
The line residual is perfect and its radical centralizer is central, so an
actor fixing the plane residual fixes the line residual as well. The existing
Borel and parabolic generation identities show that these two literal
residuals generate the projective carrier. Thus no further opposite-radical
or full-parabolic formula is an input to native representation.

Source: Aschbacher–Smith F.4.29(2), printed p.289 of refs/quasithin.pdf;
the local structure is F.1.12(7), printed pp.263–264.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitaryFiveFlagAutomorphisms
open Subgroup GreenBook.UnitaryFive Theory.SpecificGroups.UnitaryFive
variable (U : Model 4)

/-- The two literal residuals already generate the native carrier. -/
theorem residuals_generate : U.leftLocalImage ⊔ U.rightLocalImage = ⊤ := by
  have hO : U.overlap ≤ U.leftLocalImage ⊔ U.rightLocalImage := by
    rw [←U.residual_intersections_sup]
    exact sup_le_sup inf_le_left inf_le_left
  have hL : U.leftParabolic ≤ U.leftLocalImage ⊔ U.rightLocalImage := by
    rw [←U.leftLocalImage_sup_overlap]
    exact sup_le le_sup_left hO
  have hR : U.rightParabolic ≤ U.leftLocalImage ⊔ U.rightLocalImage := by
    rw [←U.rightLocalImage_sup_overlap]
    exact sup_le le_sup_right hO
  apply top_unique
  rw [←CFSG.Quasithin.Chapter5.UnitaryNativeLift.Five.parabolics_generate U]
  exact sup_le hL hR

/-- The opposite residual has central radical centralizer, in its literal subgroup type. -/
theorem leftCore_centralizer_le_center :
    centralizer (pCore 2 U.leftLocal : Set U.leftLocal) ≤ center U.leftLocal := by
  intro z hz
  apply mem_center_iff.mpr
  intro g
  apply Subtype.ext
  have hcomm : z.val ∈ centralizer (U.lineUnipotent : Set U.leftParabolic) := by
    intro u hu
    have huL : u ∈ U.leftLocal := U.lineUnipotent_le_leftLocal hu
    have huQ : (⟨u,huL⟩ : U.leftLocal) ∈ pCore 2 U.leftLocal := by
      rw [U.pCore_leftLocal_eq_lineUnipotent]
      exact hu
    exact congrArg Subtype.val (hz ⟨u,huL⟩ huQ)
  obtain ⟨c,hc⟩ := U.exists_lineTraceOne
  apply Flag.Center.commute_of_centralizes_projectiveUnipotent U.form c hc U.matrix
  · change z.val ∈ U.lineRadicalLeviSubgroup
    rw [←U.leftLocal_eq_lineRadicalLeviSubgroup]
    exact z.property
  · change g.val ∈ U.lineRadicalLeviSubgroup
    rw [←U.leftLocal_eq_lineRadicalLeviSubgroup]
    exact g.property
  · exact hcomm

/-- Fixing the entire plane residual forces agreement on the opposite endpoint as well. -/
theorem eq_one_of_rightLocalAction (a : flagAutomorphisms U)
    (ha : rightLocalAction U a = 1) : a = 1 := by
  let a' : Theory.SpecificGroups.ClassicalUnitary.NativeAmalgamActions.flagAutomorphisms
      U.rightParabolic U.leftParabolic := ⟨a.val,⟨a.property.2,a.property.1⟩⟩
  let b := Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.rightResidualAction
    U.rightParabolic U.leftParabolic a'
  have hr (x : U.Carrier) (hx : x ∈ U.rightLocalImage) : a.val x = x := by
    have hh := congrArg (fun f : MulAut U.rightLocalImage => (f ⟨x,hx⟩).val) ha
    simpa only [rightLocalAction_val,MulAut.one_apply] using hh
  have hb : b = 1 := by
    apply FlagAutomorphisms.eq_one_of_fixes_normal (pCore 2 U.leftLocal)
      (leftCore_centralizer_le_center U) b
    intro u hu
    apply Subtype.ext
    apply Subtype.ext
    change a.val u.val.val = u.val.val
    apply hr
    apply U.flagTwoSubgroup_le_rightLocalImage
    apply U.lineUnipotent_carrier_le_flagTwoSubgroup
    refine ⟨u.val,?_,rfl⟩
    exact U.map_leftCore_subtype ▸ Subgroup.mem_map_of_mem U.leftLocal.subtype hu
  have hl (x : U.leftLocalImage) : a.val x.val = x.val := by
    obtain ⟨u,rfl⟩ := U.leftLocalImageEquiv.surjective x
    exact congrArg (fun f : MulAut U.leftLocal => (f u).val.val) hb
  apply Subtype.ext
  exact Theory.SpecificGroups.ClassicalUnitary.NativeAmalgamActions.endpoint_ext
    U.leftLocalImage U.rightLocalImage (residuals_generate U) a.val 1 hl (fun x => hr x.val x.property)

/-- The literal action on the whole plane residual detects a native flag automorphism. -/
theorem rightLocalAction_injective : Function.Injective (rightLocalAction U) := by
  intro a b hab
  apply inv_mul_eq_one.mp
  apply eq_one_of_rightLocalAction U
  rw [map_mul,map_inv,hab,inv_mul_cancel]
end CFSG.Quasithin.ChapterF.UnitaryFiveFlagAutomorphisms
