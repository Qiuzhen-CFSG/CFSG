module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.MSInputs
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.G2
public import Theory.GroupTheory.CComponent.Basic
public import Theory.AtlasPort.LinearGroups.G2.BinaryNaturalPlane
public import CFSG.Quasithin.Defs

/-!
# The exceptional binary G₂ MS input

This is C.1.31(MS2)(b), on the actual generated group. The radical is the
full preimage of the marked normal root eight of the point parabolic under
the specified quotient by O₂. It is not required to be the whole two-core
of an odd-index subgroup, as in MS2(a). The two quotient markings, literal
product, relative component, characteristic-two and MS3 conditions are
retained. This structure contains no block or module conclusion.

OriginalUnitaryNoncentrality.PushingUp constructs these inputs for
L Baum(O₂(L₁T)). Whole-core reconstruction for this exceptional input is
separate from the existing SmallMSPair theorem, whose radical field is MS2(a).
Source: Aschbacher–Smith C.1.31–32, p.135; C.1.37, pp.141–143.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.G2Exceptional
universe u
variable {G : Type u} [Group G]

/-- The exact exceptional MS-pair data, with both genuine G₂ quotients. -/
structure Input (κ : GroupClass.{u}) (L R : Subgroup G) where
  sqtk : IsSQTK κ G
  fitting : generalizedFitting G = pCore 2 G
  product : ∀ g : G, ∃ l ∈ L, ∃ r ∈ R, l * r = g
  component : L.IsCComponent
  componentQuotient : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))
  quotient : (G ⧸ pCore 2 G) ≃* Atlas.G2.Model (ZMod 2)
  radical : R = Atlas.G2.BinaryCore.elementary.comap
    (quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G)))
  characteristic : MSCharacteristicCondition R

end CFSG.Quasithin.ChapterC.G2Exceptional
