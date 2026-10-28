module
public import Theory.GroupTheory.GeneralizedFitting.MovedComponent
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter
public import Theory.GroupTheory.Fitting.Core
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# The layer action with a central prime core

For a finite group with trivial prime-complement core and central p-core,
the Fitting subgroup is O_p. Centralizing the layer is then equivalent to
centralizing F*, so the generalized-Fitting centralizer theorem identifies
that centralizer with O_p. The center and solvable radical are also O_p.
Consequently the original conjugation action on the layer descends to a
faithful action of the literal quotient by O_p.

The opposite-centralizer application is in Chapter14's RecognitionOddCore.
Source: ordinary component calculus and the generalized-Fitting centralizer
theorem, Aschbacher--Smith A.3, used in 14.3.22, printed p.999.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem centralizer_layer_eq_pCore_of_central (ho : pPrimeCore p G = ⊥)
    (hc : pCore p G ≤ center G) :
    centralizer (componentLayer G : Set G) = pCore p G := by
  apply le_antisymm
  · have hF := Fitting_eq_pcore G p ho
    apply le_trans _ (centralizer_generalizedFitting_le_fitting.trans hF.le)
    apply le_centralizer_iff.mpr
    apply sup_le
    · rw [hF]
      exact hc.trans (center_le_centralizer _)
    · exact le_centralizer_iff.mp le_rfl
  · exact hc.trans (center_le_centralizer _)

theorem center_eq_pCore_of_central (ho : pPrimeCore p G = ⊥)
    (hc : pCore p G ≤ center G) : center G = pCore p G := by
  exact le_antisymm ((center_le_centralizer _).trans (centralizer_layer_eq_pCore_of_central ho hc).le) hc

theorem solvableRadical_eq_pCore_of_central (ho : pPrimeCore p G = ⊥)
    (hc : pCore p G ≤ center G) : solvableRadical G = pCore p G := by
  let : Group.IsNilpotent (pCore p G) := pCore_isPGroup.isNilpotent
  apply le_antisymm
  · exact (le_centralizer_iff.mp (componentLayer_le_centralizer_solvable_normal
      (solvableRadical G))).trans (centralizer_layer_eq_pCore_of_central ho hc).le
  · exact le_solvableRadical _ inferInstance inferInstance

noncomputable def centralPrimeCoreLayerAction (ho : pPrimeCore p G = ⊥)
    (hc : pCore p G ≤ center G) :
    (G ⧸ pCore p G) →* MulAut (componentLayer G) :=
  QuotientGroup.lift _ (MulAut.conjNormal : G →* MulAut (componentLayer G)) (by
    rw [MulAut.conjNormal_ker_eq_centralizer, centralizer_layer_eq_pCore_of_central ho hc])

theorem centralPrimeCoreLayerAction_injective (ho : pPrimeCore p G = ⊥)
    (hc : pCore p G ≤ center G) : Function.Injective (centralPrimeCoreLayerAction ho hc) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  rw [MulAut.conjNormal_ker_eq_centralizer, centralizer_layer_eq_pCore_of_central ho hc]

theorem centralPrimeCoreLayerAction_mk (ho : pPrimeCore p G = ⊥)
    (hc : pCore p G ≤ center G) (g : G) (x : componentLayer G) :
    (centralPrimeCoreLayerAction ho hc (QuotientGroup.mk' (pCore p G) g) x : G) =
      g * (x : G) * g⁻¹ := by rfl

end Theory.GroupTheory
