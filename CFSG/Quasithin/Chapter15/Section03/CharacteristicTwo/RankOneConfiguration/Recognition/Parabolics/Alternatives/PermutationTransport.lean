module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Marking
public import Theory.GroupTheory.QuotientIntersection

/-!
# Transport of component and flag intersections

The earlier containment C_I(U_I) ≤ M ∩ I makes the quotient map preserve
intersections with M ∩ I. Thus (M ∩ L)* is exactly L* ∩ (M ∩ I)*.
An eight-point equivalence marking the whole intersection by the four-pair
stabilizer therefore marks the component intersection by its even part.

Intersecting with a marked end-node parabolic gives precisely the even
part of the nested pair/four-point flag stabilizer. This retains the
component and Sylow-extension distinction required in 15.3.32. The model
equivalence and parabolic marking must still be constructed by recognition.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.11(2), 15.3.28(3), and 15.3.32(4), printed pp.1123, 1131–1133.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics
variable {G : Type*} [Group G]

/-- The genuine earlier kernel containment makes intersection with M_I commute with star image. -/
theorem starImage_inf_intersection
    (d : LocalData G) {I : Subgroup G}
    (hc : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I) (X : Subgroup G) :
    d.starImage I (X ⊓ d.MI I) =
      d.starImage I X ⊓ d.starImage I (d.MI I) := by
  have hk : (d.starMap I).ker ≤ (d.MI I).subgroupOf I := by
    rw [show (d.starMap I).ker = localActionKernel d.Z I from QuotientGroup.ker_mk' _]
    exact fun x hx => hc ⟨x.property, hx⟩
  change ((X ⊓ d.MI I).comap I.subtype).map (d.starMap I) = _
  rw [comap_inf]
  exact map_inf_of_ker_le _ _ _ hk

/-- The component intersection is exactly L* ∩ M_I*, with the original star denominator. -/
theorem component_intersection_star_eq_inf
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hc : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I) :
    d.starImage I (d.M ⊓ c.L) =
      d.starImage I c.L ⊓ d.starImage I (d.MI I) := by
  have he : c.L ⊓ d.MI I = d.M ⊓ c.L := by
    ext x
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, component_le c h.2⟩⟩
  rw [← he]
  exact starImage_inf_intersection d hc c.L

/-- Construct both component and extended markings from the full intersection marking and 15.3.11(2). -/
def middleNodePermutationMarkingOfExtended
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hc : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hL : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8))
    (hM : (d.starImage I (d.MI I)).map e.toMonoidHom =
      Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.pairStabilizer) :
    MiddleNodePermutationMarking d I c.L where
  equiv := e
  component := hL
  component_intersection := by
    rw [component_intersection_star_eq_inf d c hc, map_inf _ _ _ e.injective, hL, hM,
      inf_comm]
  extended_intersection := hM

/-- The marked component/end-parabolic intersection is the even nested flag stabilizer. -/
theorem MiddleNodePermutationMarking.flag_intersection
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (m : MiddleNodePermutationMarking d I c.L)
    (hc : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I)
    {K : Subgroup G} (hKL : K ≤ c.L)
    (hK : (d.starImage I K).map m.equiv.toMonoidHom =
      Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.fourStabilizer ⊓
        alternatingGroup (Fin 8)) :
    (d.starImage I ((d.M ⊓ c.L) ⊓ K)).map m.equiv.toMonoidHom =
      Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.flagStabilizer ⊓
        alternatingGroup (Fin 8) := by
  have he : (d.M ⊓ c.L) ⊓ K = K ⊓ d.MI I := by
    ext x
    exact ⟨fun h => ⟨h.2, h.1.1, component_le c h.1.2⟩,
      fun h => ⟨⟨h.2.1, hKL h.1⟩, h.1⟩⟩
  rw [he, starImage_inf_intersection d hc, map_inf _ _ _ m.equiv.injective,
    hK, m.extended_intersection]
  change (_ ⊓ _) ⊓ _ = (_ ⊓ _) ⊓ _
  ac_rfl

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics
