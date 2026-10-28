module

public import Theory.Representation.PSL3Two.SteinbergStructure.Duality
import all Theory.Representation.PSL3Two.SteinbergStructure.Duality

/-!
# Application formula for the existing automorphism intertwiner

This is an intentional implementation-equation extension of Duality: internal
access is used only to publish the application equation of its already defined
`autEquiv`. The concrete interchange calculation can then use that equation
without changing the shared module or exposing its construction to clients.

Source: Aschbacher–Smith J.2.3(7), printed p.434 (PDF p.445).
-/

public section
namespace BinaryLinearThree.SingerRestriction.CubicInterchange

lemma autEquiv_action (a : MulAut Group) (v : Steinberg) :
    SteinbergStructure.autEquiv a v = AutomorphismAction.steinbergAut a v := by
  unfold SteinbergStructure.autEquiv
  rfl

end BinaryLinearThree.SingerRestriction.CubicInterchange
