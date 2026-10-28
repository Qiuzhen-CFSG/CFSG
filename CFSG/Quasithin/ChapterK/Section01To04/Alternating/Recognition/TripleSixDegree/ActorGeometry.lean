module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.TripleSixDegree.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.TripleSixDegree.ActorGeometry.Inner
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.TripleSixDegree.ActorGeometry.Outer

/-!
# Elementary-actor geometry for the triple-A₆ degree bound

An elementary actor contained in the component has rank at most two and
contains an involution whose three actual conjugates generate the component.
If the actor leaves the component, an involution outside it induces a
non-inner cover automorphism and inverts the actual included cubic center.
The normality needed here comes from the source equality L = F*(G).

The resulting unconditional geometry feeds the checked linear displacement
estimate, giving binary degree at most twelve. It makes no assumption of
degree six, module recognition, or a particular ambient extension.

Source: Aschbacher–Smith K.1–K.1.3, printed pp.452–453; GLS3 5.2.3/5.2.7.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Atlas.Codes

namespace CFSG.Quasithin.ChapterK.Alternating.TripleSixReduction
universe u v

/-- The source input supplies the required inner or outer geometry for every actor. -/
theorem cubicActorGeometry : CubicActorGeometry.{u,v} := by
  intro G V _ _ _ _ _ ρ K L h e A hA
  classical
  by_cases hAL : A ≤ L
  · exact actorGeometry_of_le e hA hAL
  · let : L.Normal := by rw [h.fitting]; infer_instance
    let := h.irreducible
    exact actorGeometry_of_not_le ρ h.faithful e hA hAL

/-- The proved geometry discharges the group-theoretic premise of the actual
ambient cubic degree estimate. -/
theorem finrank_le_twelve {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}} {L : Subgroup G}
    (h : Input ρ K L) (e : L ≃* HexEvenAutomorphisms) :
    Module.finrank (ZMod 2) V ≤ 12 :=
  finrank_le_twelve_of_actorGeometry ρ h e (cubicActorGeometry ρ K L h e)

end CFSG.Quasithin.ChapterK.Alternating.TripleSixReduction
