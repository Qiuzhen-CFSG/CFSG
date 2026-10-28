module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.Catalogue
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.LocalSections
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.CubicControl
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.Geometry
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.SixGeometry
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.G2

/-!
# The actual subgroup in the parabolic part of 15.3.49(l)

The local calculation uses T₀ = T ∩ L and P = Y₀*T₀*. It establishes
the index [P:T₀*] = 3, minimality above T₀*, T*-invariance, and the
intersection with L*. In the A₆ branch the supplied component equivalence
identifies P with a geometric parabolic of Sp₄(2) restricted to Sp₄(2)′.
The point and plane stabilizers are identified by the actual polar action.

The linear one-node flag construction and the derived G₂ recognition
remain required for the other Lie-type branches. No full assertion of (l)
is made here. The component-closure and model-classification hypotheses
remain with the assembly owner, as do the exceptional A₇ and triple-cover
alternatives, for which the source asserts no parabolic conclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1143–1145, especially clause (l) on p.1144.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter1
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.Binary

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification

/-- The A₆ branch of the local parabolic identification, with the same component
equivalence followed by the canonical equivalence to the derived binary model. -/
theorem alternating_six_parabolic {G : Type*} [Group G] [Finite G]
    (H M L Y₀ T : Subgroup G) (c : LocalControl H M Y₀ T)
    (hgen : H = reducedOvergroup L Y₀ T) (hclosed : localSpan L T = L)
    (hYL₀ : Y₀ ≤ localSpan L T) (hL : (L.subgroupOf H).IsCComponent)
    (e : starImage H L ≃* A6) :
    starImage H (T ⊓ L) ⋖ ModelExclusions.componentParabolic H L Y₀ T ∧
      starImage H T ≤ normalizer
        (ModelExclusions.componentParabolic H L Y₀ T : Set (H ⧸ pCore 2 H)) ∧
      ∃ (g : A6) (i : Bool),
        ((ModelExclusions.componentParabolic H L Y₀ T).subgroupOf (starImage H L)).map
          (e.trans Six.alternatingEquivDerived).toMonoidHom =
        ((stabilizer (Six.markedSpace i)).map
          (MulAut.conj (symmetricSixEquiv g.val)).toMonoidHom).subgroupOf
            (commutator (Sp (ZMod 2))) := by
  obtain ⟨hs, hPL, hi, hmin, hinv⟩ :=
    parabolic_local H M L Y₀ T c hgen hclosed hYL₀ hL
  exact ⟨hmin, hinv, Six.derived_position_intrinsic (starImage H L)
    (starImage H (T ⊓ L)) (ModelExclusions.componentParabolic H L Y₀ T)
    e hs le_sup_right hPL hi⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification
