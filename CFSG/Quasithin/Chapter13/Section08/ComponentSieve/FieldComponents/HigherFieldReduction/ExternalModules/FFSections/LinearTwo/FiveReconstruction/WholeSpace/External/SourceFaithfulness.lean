module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.WholeSpace.External.MovedFaithfulness
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.SeedAction

/-!
# Source inputs for faithfulness on the exceptional moved orbit

The source factorization H = K(L₁T), with L₁T solvable, makes the image of
L₁T surject onto H*/K*. All maps below are the literal two-core quotient
and subsequent component quotient. Relative normality of K in H supplies
normality of K*. The selected 13.8.14 residual alternative, transported by
`twoFittingResidual_star`, gives F(H*) ≤ X*.

Applying the coordinate-kernel argument proves faithfulness on the given
subrepresentation W of the literal SeedAction.Space H V₃ V₁. The adapter
takes the already reconstructed FactorCoordinates on W and the marked
cubic image. In the source application W is the actual two-conjugate orbit
[U,K*]; neither W = U nor faithfulness on W is an input. The original
representation and its subrepresentation are retained without replacing
their carriers or quotient maps. The constituent and multiplicity data
that produce these coordinates remain obligations of the reconstruction
owner; they are not replaced by assumptions about a whole-U tensor model.

The final adapter selects X = L₁ or X = L₁,+ from the actual local carrier,
using `Structure.selected_fitting_alternative`. Its earlier inputs are the
source factorization, solvability of L₁T, and the complete 13.8.14 output.
Full marked coordinates and the quadratic endpoint remain with the
reconstruction owner. No whole-space generation conclusion is asserted.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.14–16,
printed pp.951–952, and the external L₂(4) branch of 13.8.20, printed p.954.
-/

public section

open Subgroup Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section08
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.WholeSpace.External

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Relative component normality descends through the literal two-core quotient. -/
theorem source_component_star_normal (H K : Subgroup G) [(K.subgroupOf H).Normal] :
    (Source.starImage H K).Normal := by
  unfold Source.starImage
  infer_instance

attribute [local instance] source_component_star_normal

omit [Finite G] in
/-- The solvable source supplement surjects onto the actual component quotient. -/
theorem source_component_quotient_solvable (H K L₁ T : Subgroup G)
    [(K.subgroupOf H).Normal]
    (hgen : H = K ⊔ (L₁ ⊔ T)) [Group.IsSolvable (L₁ ⊔ T : Subgroup G)] :
    Group.IsSolvable (Source.Hstar H ⧸ Source.starImage H K) := by
  have hKH : K ≤ H := by rw [hgen]; exact le_sup_left
  have hPH : L₁ ⊔ T ≤ H := by rw [hgen]; exact le_sup_right
  let P := Source.starImage H (L₁ ⊔ T)
  let : Group.IsSolvable P := by
    let : Group.IsSolvable ((L₁ ⊔ T).subgroupOf H) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe hPH).toMonoidHom) (subgroupOfEquivOfLe hPH).injective
    exact Group.isSolvable_of_surjective
      ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective ((L₁ ⊔ T).subgroupOf H))
  have hGP : Source.starImage H K ⊔ P = ⊤ := by
    change Source.starImage H K ⊔ Source.starImage H (L₁ ⊔ T) = ⊤
    have he : Source.starImage H (K ⊔ (L₁ ⊔ T)) =
        Source.starImage H K ⊔ Source.starImage H (L₁ ⊔ T) := by
      unfold Source.starImage
      rw [subgroupOf_sup hKH hPH, Subgroup.map_sup]
    rw [← he, ← hgen]
    simp [Source.starImage, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let q := QuotientGroup.mk' (Source.starImage H K)
  have hmap : P.map q = ⊤ := by
    have he := congrArg (map q) hGP
    simpa only [q, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using he
  apply Group.isSolvable_of_surjective (f := q.comp P.subtype)
  intro y
  have hy : y ∈ P.map q := by rw [hmap]; trivial
  obtain ⟨p, hp, he⟩ := hy
  exact ⟨⟨p, hp⟩, he⟩

/-- The selected residual alternative of 13.8.14 bounds F(H*) by the actual X*. -/
theorem source_fitting_le_cubic (H X : Subgroup G)
    (hfit : Components.Fitting.twoFittingResidual H = ⊥ ∨
      Components.Fitting.twoFittingResidual H = X) :
    fittingSubgroup (Source.Hstar H) ≤ Source.starImage H X := by
  rw [← Components.Fitting.twoFittingResidual_star H]
  rcases hfit with hfit | hfit
  · simp [hfit, Source.starImage]
  · rw [hfit]

variable (H K X L₁ T V₃ V₁ : Subgroup G)
  [(K.subgroupOf H).Normal]
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
  (s : Equiv.Perm (Fin 3) →* Source.Hstar H)
  (W : Subrepresentation ρ)
  (c : FactorCoordinates W.toRepresentation (Source.starImage H K) s)

/-- Actual coordinates on W, the solvable supplement, and the selected earlier
Fitting alternative imply injectivity of both the coordinates and the W-action. -/
theorem source_moved_faithfulness_of_selected_fitting
    (hgen : H = K ⊔ (L₁ ⊔ T)) [Group.IsSolvable (L₁ ⊔ T : Subgroup G)]
    (hfit : Components.Fitting.twoFittingResidual H = ⊥ ∨
      Components.Fitting.twoFittingResidual H = X)
    (hmark : (alternatingGroup (Fin 3)).map s = Source.starImage H X) :
    Function.Injective c.ambientHom ∧ Function.Injective W.toRepresentation := by
  let : Group.IsSolvable (Source.Hstar H ⧸ Source.starImage H K) :=
    source_component_quotient_solvable H K L₁ T hgen
  have hi := c.ambientHom_injective_of_small_fitting (Source.starImage H X) hmark
    (source_fitting_le_cubic H X hfit)
  exact ⟨hi, c.action_injective_of_ambientHom_injective hi⟩

/-- Source-facing faithfulness on the moved orbit. The actual ordinary or
covered local carrier selects X from the complete earlier 13.8.14 alternatives;
quotient solvability and the star Fitting bound are both derived. -/
theorem source_moved_faithfulness (L L₁plus : Subgroup G)
    (hgen : H = K ⊔ (L₁ ⊔ T)) [Group.IsSolvable (L₁ ⊔ T : Subgroup G)]
    (hlocal : (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = L₁) ∨
      (SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧ X = L₁plus))
    (hfit : SolvableExclusion.ResidualAlternative L L₁ L₁plus
      (Components.Fitting.twoFittingResidual H))
    (hmark : (alternatingGroup (Fin 3)).map s = Source.starImage H X) :
    Function.Injective c.ambientHom ∧ Function.Injective W.toRepresentation :=
  source_moved_faithfulness_of_selected_fitting H K X L₁ T V₃ V₁ ρ s W c hgen
    (Structure.selected_fitting_alternative H L L₁ L₁plus X hlocal hfit) hmark

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.WholeSpace.External

end
