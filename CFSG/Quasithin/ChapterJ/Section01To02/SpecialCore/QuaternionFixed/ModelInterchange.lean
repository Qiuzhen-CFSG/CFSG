module

public import Theory.Representation.PSL3Two.SingerRestriction.CubicInterchange
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.QuaternionFixed.InterchangeLift

/-!
# The concrete Steinberg interchange in the quaternion argument

Apply the actual model calculation to singerImage, cubicImage and the literal
Steinberg-coordinate image of C_S(s). The existing five-space theorem supplies
disjointness and transitivity; conjugation in the original group supplies
Singer invariance. Thus the only remaining input is the preceding full
commutator conclusion, already explicit in the quaternion assembly.

This discharges exactly the hmove premise of
cubicFixedQ_equiv_quaternion_of_model_interchange in InterchangeLift. The
quaternion recognition and its remaining ambient hypotheses stay with that
assembly owner.

Source: Aschbacher–Smith J.2.3(7), printed p.434 (PDF p.445),
combined manuscript of 1 March 2004.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open Representation.RegularCyclicNormalClosure
namespace CFSG.Quasithin.ChapterJ.SpecialCore
variable {G : Type*} [Group G] [Finite G]
noncomputable section
local instance : AddCommGroup BinaryLinearThree.Steinberg := inferInstance
local instance : Module (ZMod 2) BinaryLinearThree.Steinberg := inferInstance

/-- The literal model-movement premise of
`cubicFixedQ_equiv_quaternion_of_model_interchange`, with every model
hypothesis discharged by the preceding Singer centralizer geometry. -/
theorem SingerChoice.model_interchange (d : LocalSetup G)
    (B : Sylow 3 d.toTypeRuSetup.L₁) (c : SingerChoice d.toTypeRuSetup B)
    (hfull : ∀ t : d.toTypeRuSetup.S, (t : G) ∉ d.V →
      ⁅zpowers (t : G),d.toTypeRuSetup.S⁆ = d.V)
    (s : G) (hs : s ∈ fixedCore d.toTypeRuSetup c.B7) (hs1 : s ≠ 1) :
    ∀ v : BinaryLinearThree.Steinberg,
      v ∈ displacementSpan BinaryLinearThree.S (singerImage d.toTypeRuSetup B c)
        (sectionImage d.toTypeRuSetup (d.toTypeRuSetup.S ⊓ centralizer ({s} : Set G))) →
      v ≠ 0 → v ∈ fixedSpace BinaryLinearThree.S (cubicImage d.toTypeRuSetup B) →
      ∃ g : BinaryLinearThree.Group, g ∈ normalizer (cubicImage d.toTypeRuSetup B) ∧
        BinaryLinearThree.S g v ≠ v := by
  let D := d.toTypeRuSetup
  let C := D.S ⊓ centralizer ({s} : Set G)
  let A := sectionImage D C
  have hB := cubicSubgroup_card D B d.card_Z (d.center_eq.le.trans inf_le_left)
  have hr := c.centralizerImage_fiveSpace D B hB hfull s hs hs1
  have hA : ∀ h ∈ singerImage D B c, ∀ a ∈ A, BinaryLinearThree.S h a ∈ A := by
    intro h hh
    obtain ⟨b,rfl⟩ := hh
    exact sectionImage_invariant D C (inclusion c.le_L b)
      (c.normalizes_coreCentralizer D B s hs b.property)
  exact BinaryLinearThree.SingerRestriction.CubicInterchange.exists_moving_normalizer
    (singerImage D B c) (cubicImage D B) (singerImage_card D B c)
    (cubicImage_card D B hB) (cubicImage_normalizes_singerImage D B c)
    (displacementSpan BinaryLinearThree.S (singerImage D B c) A)
    (BinaryLinearThree.SingerRestriction.FiveSpace.moved_mem (singerImage D B c) A hA)
    hr.2.2.1 hr.2.2.2.2
end
end CFSG.Quasithin.ChapterJ.SpecialCore
