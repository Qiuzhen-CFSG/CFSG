module

public import Theory.GroupTheory.GeneralizedFitting.OrdinaryCentralizerOrbit
public import Theory.GroupTheory.SylowPointwiseSection
public import CFSG.Quasithin.ChapterI.Section03.Balance

/-!
# The ordinary-component part of I.3 balance

The genuine two-layer bound of GLS II 5.17 puts an ordinary component of
an involution centralizer in the ambient layer when the odd core is trivial.
The central-product orbit theorem then supplies the ambient ordinary
component orbit required by the Chapter 2 Bender argument.

The two independent earlier-source inputs are retained literally: solvability
of the Sylow-two pointwise automorphism fixer of every finite simple group,
and the internal centralizer specialization of 5.17 under S₂. Their producers
are qt-i03-two-schreier and qt-i03-two-layer-balance. No B₂ projection result
is needed for this ordinary-component conclusion. Full I.3 remains with its
existing assembly owner.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterI.OrdinaryBalance
open Subgroup Theory.GroupTheory
universe u

/-- The unconditional finite-simple endpoint supplied by the S₂ producer. -/
def SimpleSylowFixerSolvability : Prop :=
  ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S],
    ∀ P : Sylow 2 S, Group.IsSolvable (fixingSubgroup (MulAut S) (P : Set S))

/-- The literal internal-centralizer specialization of GLS II 5.17. -/
def TwoLayerCentralizerBalance : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], HasTwoSchreier H →
    ∀ P : Subgroup H, IsPGroup 2 P →
      (twoComponentLayer (centralizer (P : Set H))).map
        (centralizer (P : Set H)).subtype ≤ twoComponentLayer H

/-- The finite-simple input supplies S₂ on the actual section maps. -/
theorem hasTwoSchreier_of_simpleSylowFixer
    (sourceS2 : SimpleSylowFixerSolvability.{u})
    (H : Type u) [Group H] [Finite H] : HasTwoSchreier H := by
  intro U S _ _ f hf P
  let : Finite S := Finite.of_surjective f hf
  exact sourceS2 S P

/-- Once the earlier layer bound is available, ordinary orbit selection is
proved without assuming its conclusion or any projected-component assertion. -/
theorem ordinary_orbit_of_twoLayer_bound {H : Type u} [Group H] [Finite H]
    (ho : pPrimeCore 2 H = ⊥) (t : H) (D : Subgroup H)
    (hD : IsComponentIn D (centralizer ({t} : Set H)))
    (hbalance : (twoComponentLayer (centralizer ({t} : Set H))).map
      (centralizer ({t} : Set H)).subtype ≤ twoComponentLayer H) :
    ∃ J : Subgroup H, IsComponent H J ∧ D ≤ componentOrbit J (zpowers t) := by
  have hc : centralizer (zpowers t : Set H) = centralizer ({t} : Set H) := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hD' : IsComponentIn D (centralizer (zpowers t : Set H)) := by
    simpa only [hc] using hD
  have hb : (twoComponentLayer (centralizer (zpowers t : Set H))).map
      (centralizer (zpowers t : Set H)).subtype ≤ twoComponentLayer H := by
    exact (congrArg (fun U : Subgroup H =>
      (twoComponentLayer U).map U.subtype ≤ twoComponentLayer H) hc).mpr hbalance
  exact hD.le_componentOrbit_of_le_componentLayer
    (Balance.ordinary_local_component_le_layer_of_twoLayer_bound ho (zpowers t) hD' hb)

/-- The ordinary-component consequence of the two universal earlier-source
inputs. The original involution and the literal cyclic orbit are retained. -/
theorem ordinary_orbit_of_source_inputs
    (sourceS2 : SimpleSylowFixerSolvability.{u})
    (source517 : TwoLayerCentralizerBalance.{u})
    {H : Type u} [Group H] [Finite H] (ho : pPrimeCore 2 H = ⊥)
    (t : H) (ht : orderOf t = 2) (D : Subgroup H)
    (hD : IsComponentIn D (centralizer ({t} : Set H))) :
    ∃ J : Subgroup H, IsComponent H J ∧ D ≤ componentOrbit J (zpowers t) := by
  have hp : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ht, pow_one])
  have hb := source517 H (hasTwoSchreier_of_simpleSylowFixer sourceS2 H) (zpowers t) hp
  have hc : centralizer (zpowers t : Set H) = centralizer ({t} : Set H) := by
    rw [zpowers_eq_closure, centralizer_closure]
  exact ordinary_orbit_of_twoLayer_bound ho t D hD
    ((congrArg (fun U : Subgroup H =>
      (twoComponentLayer U).map U.subtype ≤ twoComponentLayer H) hc).mp hb)

end CFSG.Quasithin.ChapterI.OrdinaryBalance
