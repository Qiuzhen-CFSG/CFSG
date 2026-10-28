module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.Spanning
public import Theory.SpecificGroups.Monster.Construction.LocalC.Action

/-!
# Conditional assembly on the literal zero space

A constructed action on the marked tensor model and a constructed odd-family
comparison transport to an action on the existing `ZeroSpace`. The kernel,
bilinear form and N1 inclusion equations pass through this explicit comparison.
`modelBeta` is exactly the pullback of the fixed `griessBeta`; preservation
of it passes to the literal zero inclusion as well.

These lemmas do not construct the model action or the odd comparison and do
not assert their invariance premises. They give the final assembly owner one
place to instantiate the independently proved source branches. In particular,
there is no unconditional N-action export in this module yet.

Source: Aschbacher, *Sporadic Groups*, the transport after 29.8 and 29.9,
printed pp. 157--158. The action construction uses left function composition.
-/

@[expose] public section
open Atlas.Codes Atlas.Fischer
open Sporadic.Monster Sporadic.Monster.Construction
open LocalC ShortFamilies TrialitySpin SpinActions
open scoped TensorProduct
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction

/-- Conditional assembly; the actual odd comparison and model action are
independent constructions, not fields asserted by this definition. -/
def representationOfModel (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (ρ : Representation ℝ N ModelSpace) : Representation ℝ N ZeroSpace :=
  (zeroToModel e).symm.conjRingEquiv.toMonoidHom.comp ρ

theorem representationOfModel_apply (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (ρ : Representation ℝ N ModelSpace) (g : N) (v : ZeroSpace) :
    representationOfModel e ρ g v = (zeroToModel e).symm (ρ g (zeroToModel e v)) := rfl

theorem zeroToModel_representationOfModel (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (ρ : Representation ℝ N ModelSpace) (g : N) (v : ZeroSpace) :
    zeroToModel e (representationOfModel e ρ g v) = ρ g (zeroToModel e v) :=
  (zeroToModel e).apply_symm_apply _

theorem representationOfModel_K (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (ρ : Representation ℝ N ModelSpace) (hK : ∀ g ∈ TrialitySpin.K, ρ g = 1)
    (g : N) (hg : g ∈ TrialitySpin.K) : representationOfModel e ρ g = 1 := by
  change (zeroToModel e).symm.conjRingEquiv.toMonoidHom (ρ g) = 1
  rw [hK g hg, map_one]

theorem representationOfModel_gamma (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (he : ∀ v w : oddSpace, tensorTwoForm (e v) (e w) =
      shortForm sourceLatticeComparison v.val w.val)
    (ρ : Representation ℝ N ModelSpace)
    (hρ : ∀ g v w, modelGamma (ρ g v) (ρ g w) = modelGamma v w)
    (g : N) (v w : ZeroSpace) :
    zeroGamma (representationOfModel e ρ g v) (representationOfModel e ρ g w) =
      zeroGamma v w := by
  rw [← zeroToModel_isometry e he, zeroToModel_representationOfModel,
    zeroToModel_representationOfModel, hρ, zeroToModel_isometry e he]

/-- Transport the existing beta; no substitute form is introduced. -/
def modelBeta (e : oddSpace ≃ₗ[ℝ] TensorTwo) : Griess.TrilinearForm ModelSpace :=
  Griess.pullback3 griessBeta
    (zeroInclusion.comp (zeroToModel e).symm.toLinearMap)
    (zeroInclusion.comp (zeroToModel e).symm.toLinearMap)
    (zeroInclusion.comp (zeroToModel e).symm.toLinearMap)


theorem modelBeta_apply (e : oddSpace ≃ₗ[ℝ] TensorTwo) (u v w : ModelSpace) :
    modelBeta e u v w = griessBeta
      (zeroInclusion ((zeroToModel e).symm u))
      (zeroInclusion ((zeroToModel e).symm v))
      (zeroInclusion ((zeroToModel e).symm w)) := rfl

theorem representationOfModel_beta (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (ρ : Representation ℝ N ModelSpace)
    (hρ : ∀ g u v w, modelBeta e (ρ g u) (ρ g v) (ρ g w) = modelBeta e u v w)
    (g : N) (u v w : ZeroSpace) :
    griessBeta (zeroInclusion (representationOfModel e ρ g u))
      (zeroInclusion (representationOfModel e ρ g v))
      (zeroInclusion (representationOfModel e ρ g w)) =
      griessBeta (zeroInclusion u) (zeroInclusion v) (zeroInclusion w) := by
  have h := hρ g (zeroToModel e u) (zeroToModel e v) (zeroToModel e w)
  simpa only [representationOfModel_apply, modelBeta_apply, (zeroToModel e).symm_apply_apply] using h


/-- The literal model inclusion, to state the independent N1 comparison. -/
def modelInclusion (e : oddSpace ≃ₗ[ℝ] TensorTwo) : ModelSpace →ₗ[ℝ] GriessSpace :=
  zeroInclusion.comp (zeroToModel e).symm.toLinearMap

theorem modelInclusion_zeroToModel (e : oddSpace ≃ₗ[ℝ] TensorTwo) (v : ZeroSpace) :
    modelInclusion e (zeroToModel e v) = zeroInclusion v := by
  simp [modelInclusion]

theorem representationOfModel_n1 (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (ρ : Representation ℝ N ModelSpace)
    (hρ : ∀ (g : N1) (v : ModelSpace), modelInclusion e (ρ g.val v) =
      cRepresentation (n1ToC g) (modelInclusion e v)) (g : N1) (v : ZeroSpace) :
    zeroInclusion (representationOfModel e ρ g.val v) =
      cRepresentation (n1ToC g) (zeroInclusion v) := by
  have h := hρ g (zeroToModel e v)
  rw [modelInclusion_zeroToModel] at h
  exact h


/-- To check literal N1 compatibility it suffices to check the three source
families. The final assembly must prove these equations for its constructed action. -/
theorem representationOfModel_n1_of_generators (e : oddSpace ≃ₗ[ℝ] TensorTwo)
    (ρ : Representation ℝ N ModelSpace)
    (ho : ∀ (g : N1) x b,
      zeroInclusion (representationOfModel e ρ g.val (zeroOdd x b)) =
        cRepresentation (n1ToC g) (zeroInclusion (zeroOdd x b)))
    (ht : ∀ (g : N1) x b,
      zeroInclusion (representationOfModel e ρ g.val (zeroTwo (pointVector x) (delta2 b))) =
        cRepresentation (n1ToC g) (zeroInclusion (zeroTwo (pointVector x) (delta2 b))))
    (hh : ∀ (g : N1) x b,
      zeroInclusion (representationOfModel e ρ g.val (zeroThree (pointVector x) (delta3 b))) =
        cRepresentation (n1ToC g) (zeroInclusion (zeroThree (pointVector x) (delta3 b))))
    (g : N1) (v : ZeroSpace) :
    zeroInclusion (representationOfModel e ρ g.val v) =
      cRepresentation (n1ToC g) (zeroInclusion v) := by
  have h : zeroInclusion.comp (representationOfModel e ρ g.val) =
      (cRepresentation (n1ToC g)).comp zeroInclusion :=
    zeroSpace_ext _ _ (ho g) (ht g) (hh g)
  exact LinearMap.congr_fun h v

end Sporadic.Monster.Construction.NMonomial.ZeroAction
