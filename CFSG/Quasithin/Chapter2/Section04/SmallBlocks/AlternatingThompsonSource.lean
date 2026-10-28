module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingNormalizerSource
public import CFSG.Quasithin.ChapterC.Section06.Thompson.AlternatingOriginal
/-!
# Thompson stability for the selected alternating-five block

The original Chapter 2 configuration supplies the actual C.5 action and the
noncommuting conjugate module for every index-two overgroup of the selected
Sylow subgroup inside T. The C.6.1 four-family count therefore applies with
no extra geometry or action hypotheses.

Source: Aschbacher–Smith 2.4.5(3), C.6.1 case (beta), printed pp.528,165.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_thompson_source
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (htype : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (M₀ : Subgroup G) (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    elementaryAbelianMaxJ M₀ = elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) := by
  obtain ⟨c,h,x,hx,hnc⟩ := d.single_alternating_configuration hG T hST hsingle htype
    M₀ hSM hMT hi
  exact ChapterC.Section06.alternating_thompson_stable_from_original c h hi x hx hnc
end CFSG.Quasithin.Chapter2
