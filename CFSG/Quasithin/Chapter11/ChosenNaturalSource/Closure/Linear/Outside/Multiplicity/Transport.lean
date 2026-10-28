module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Setup
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.NaturalSum.Action

/-!
# The two literal closure quotients

The quotient of W by V₁ is identified with the image of W in G₁/V₁ by
factoring the original restricted quotient map. The identification intertwines
conjugation, so action kernels and natural-module markings can be transported
without changing the source action.

Source: Aschbacher--Smith, 11.5.7, printed p.782.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

/-- The bridge uses the actual map into G₁/V₁. -/
def quotientTildeEquiv : (E.W ⧸ E.V₁.subgroupOf E.W) ≃* E.tilde E.W :=
  (QuotientGroup.quotientMulEquivOfEq (E.tildeProjection_kernel E.W
    (closure_le_point_normalizer E)).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (E.tildeProjection E.W (closure_le_point_normalizer E))
        (E.tildeProjection_surjective E.W (closure_le_point_normalizer E)))

theorem quotientTildeEquiv_apply_mk (w : E.W) :
    quotientTildeEquiv E (QuotientGroup.mk' (E.V₁.subgroupOf E.W) w) =
      E.tildeProjection E.W (closure_le_point_normalizer E) w := rfl

/-- The quotient identification intertwines the original conjugation actions. -/
theorem quotientTildeEquiv_action (A : Subgroup G) (hA : A ≤ E.G₁)
    (a : A) (w : E.W ⧸ E.V₁.subgroupOf E.W) :
    quotientTildeEquiv E (quotientAction E A hA a w) =
      E.tildeConjugation E.W A hA
        (hA.trans (le_normalizer_conjugateSpanBy V E.G₁)) a (quotientTildeEquiv E w) := by
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (E.V₁.subgroupOf E.W) w
  rw [quotientAction_apply_mk, quotientTildeEquiv_apply_mk, quotientTildeEquiv_apply_mk]
  apply Subtype.ext
  simp only [Geometry.tildeProjection, Geometry.tildeConjugation_apply]
  rfl

/-- Restricting the ambient action gives the same homomorphism, not merely
an isomorphic action. -/
theorem quotientAction_restrict (A : Subgroup G) (hA : A ≤ E.G₁) :
    quotientAction E A hA = (quotientAction E E.G₁ le_rfl).comp (inclusion hA) := by
  ext a w
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (E.V₁.subgroupOf E.W) w
  simp only [MonoidHom.comp_apply, quotientAction_apply_mk]
  rfl

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
