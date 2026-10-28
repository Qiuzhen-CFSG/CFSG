module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.Residuals
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane.Recognition

/-!
# Recognizing the actual component actor

The component actor is the literal two-residual O²(Y₊ ∩ L). If its
commutators generate an invariant four-group W which is self-centralizing
in L, then W is normal and self-centralizing in that actor. Two-perfectness
then identifies the actor with A₄. The self-centralization premise is a
separate concrete-model calculation, not an assumed actor identification.

Source: Aschbacher--Smith, proof of 15.3.40, printed p.1138.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane

/-- The commutator plane and a model centralizer calculation recognize
the actual two-residual actor. -/
theorem component_actor_alternating_of_selfCentralizing
    {G : Type*} [Group G] [Finite G] {Yplus L S W : Subgroup G}
    [IsKleinFour W] (hWS : W ≤ S) (hWL : W ≤ L)
    (hSY : S ≤ normalizer (Yplus : Set G))
    (hAN : componentFactor Yplus L ≤ normalizer (W : Set G))
    (hgen : ⁅W, componentFactor Yplus L⁆ = W)
    (hc : L ⊓ centralizer (W : Set G) ≤ W) :
    Nonempty (componentFactor Yplus L ≃* alternatingGroup (Fin 4)) := by
  let A := componentFactor Yplus L
  have hWA : W ≤ A := by
    rw [← hgen]
    exact le_normalizer_iff_commutator_le_right.mp
      (normalizes_componentFactor (hWS.trans hSY) (hWL.trans L.le_normalizer))
  let K := W.subgroupOf A
  let : K.Normal := (normal_subgroupOf_iff_le_normalizer hWA).mpr hAN
  let e : K ≃* W := subgroupOfEquivOfLe hWA
  let : IsKleinFour K :=
    ⟨(Nat.card_congr e.toEquiv).trans IsKleinFour.card_four,
      (Monoid.exponent_eq_of_mulEquiv e).trans IsKleinFour.exponent_two⟩
  have hK : centralizer (K : Set A) = K := by
    apply le_antisymm
    · intro x hx
      apply hc
      refine ⟨componentFactor_le Yplus L x.property, ?_⟩
      intro w hw
      exact congrArg Subtype.val (hx (⟨w, hWA hw⟩ : A) hw)
    · intro x hx y hy
      exact congrArg Subtype.val
        ((IsKleinFour.isMulCommutative (G := K)).is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  exact alternating_four_of_pPerfect_selfCentralizing_kleinFour
    K hK (componentFactor_isPPerfect Yplus L)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane
