module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.RudvalisExclusion.SmallModuleRecognition.Inputs
public import Mathlib.RepresentationTheory.Character

/-!
# The remaining scalar calculation for the degree-28 intertwiner

The comparison below concerns the traces of the actual representations on
all odd-order elements. It is a proof obligation, not an asserted character
table. `GeneratorIntertwiner` proves that it suffices, using the separately
proved irreducibility of the fixed matrix action and Jacobson density over
the original coefficient field. No semisimplicity of the whole group algebra
or division by the group order is used.

Source: Hiss--Malle, Low-dimensional representations of quasi-simple groups,
corrected Table 2, p.102, the binary degree-28 Ru row. GM02 Proposition 5.1's
Ru paragraph uses the small degree but does not prove this marked comparison.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion
namespace SmallModuleRecognitionInputs
open Theory.GroupTheory
universe v

/-- Exhaustive equality of binary traces on the 2-regular elements, with
the original carrier and the literal fixed matrix action. -/
def Degree28OddTraceComparison : Prop :=
  ∀ (e : Rudvalis.Model ≃* standardGroup),
    (e Rudvalis.a).val = generatorA → (e Rudvalis.b).val = generatorB →
    IsQuasisimple Rudvalis.Model →
    ∀ (V : Type v) [AddCommGroup V] [Module (ZMod 2) V]
      [FiniteDimensional (ZMod 2) V] (σ : Representation (ZMod 2) Rudvalis.Model V),
      Function.Injective σ → σ.IsAbsolutelyIrreducible →
      Module.finrank (ZMod 2) V = 28 →
      ∀ g : Rudvalis.Model, ¬ 2 ∣ orderOf g →
        σ.character g = Representation.character (standardRepresentation.comp e.toMonoidHom) g

end SmallModuleRecognitionInputs
end CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion
