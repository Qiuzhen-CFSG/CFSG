module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.ShortA2.SourceModel.Blocks
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.ShortA2.Model
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.Transport
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.Coordinates
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# From a concrete block chart to the literal short F4 subgroup

The faithful action from `Blocks` is transported to the actual F4 Geck carrier
and converted to matrix units. Signed generator comparisons place its entire
image in the root-generated F4 cover, using the proved generation of SL3.
Faithfulness survives both transport and restriction. The final application
uses `pairModelLift` on the literal subgroup at nodes 2 and 3 and proves its
unchanged signed-generator equation.

The change of basis and its four signed curve identities remain explicit
inputs. They are a concrete linear-algebra problem for the fixed block action,
not an assumed SL3-to-F4 homomorphism. This conditional construction does not
assert the missing chart or the unconditional `ShortA2.sourceModel`.
No global descent, quotient identification, or division by three is used.

Source: GLS3 §2.6.2, the common-lattice subsystem construction, and the F4
inclusion used in Aschbacher--Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.ShortA2.SourceBlocks
open Theory.AlgebraicGroup.StandardRootSystem
open WordDescent Matrix
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _

/-- The literal Cartan-plus-root index set of the F4 cover. -/
abbrev GeckIndex := typeF4RootPairing_base.support ⊕ typeF4Roots
abbrev GeckSpace (F : Type*) := GeckIndex → F
variable (F : Type*) [Field F]

/-- Matrix units and linear automorphisms of the original coordinate space. -/
def matrixEquiv : (Matrix GeckIndex GeckIndex F)ˣ ≃*
    (GeckSpace F ≃ₗ[F] GeckSpace F) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (GeckSpace F))

@[simp] theorem matrixEquiv_apply (g : (Matrix GeckIndex GeckIndex F)ˣ)
    (v : GeckSpace F) : matrixEquiv F g v = g.val *ᵥ v := rfl

variable (e : Space F ≃ₗ[F] GeckSpace F)

/-- Transport of the already constructed block action along a supplied chart. -/
def transported : Model F →* (GeckSpace F ≃ₗ[F] GeckSpace F) where
  toFun g := e.symm.trans ((action F g).trans e)
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

@[simp] theorem transported_apply (g : Model F) (v : GeckSpace F) :
    transported F e g v = e (action F g (e.symm v)) := rfl

theorem transported_injective : Function.Injective (transported F e) := by
  intro g h he
  apply action_injective F
  apply LinearEquiv.ext
  intro v
  apply e.injective
  have hv := DFunLike.congr_fun he (e v)
  simpa only [transported_apply, LinearEquiv.symm_apply_apply] using hv

/-- The transported action, as actual invertible Geck-indexed matrices. -/
def matrixHom : Model F →* (Matrix GeckIndex GeckIndex F)ˣ :=
  (matrixEquiv F).symm.toMonoidHom.comp (transported F e)

theorem matrixHom_injective : Function.Injective (matrixHom F e) :=
  (matrixEquiv F).symm.injective.comp (transported_injective F e)

/-- The precise remaining coordinate identity, for both signs and both nodes. -/
def Intertwines : Prop := ∀ (s k : Bool) (t : F) (v : Space F),
  e (action F (modelGenerator F s k t) v) =
    (coverSimple F s (pairNode 2 3 k) t).val.val *ᵥ e v

variable (he : Intertwines F e)
include he

theorem matrixHom_generator (s k : Bool) (t : F) :
    matrixHom F e (modelGenerator F s k t) =
      (coverSimple F s (pairNode 2 3 k) t).val := by
  apply (matrixEquiv F).injective
  change matrixEquiv F ((matrixEquiv F).symm
    (transported F e (modelGenerator F s k t))) = _
  rw [MulEquiv.apply_symm_apply]
  apply LinearEquiv.ext
  intro v
  obtain ⟨w, rfl⟩ := e.surjective v
  simpa only [transported_apply, LinearEquiv.symm_apply_apply, matrixEquiv_apply] using
    he s k t w

theorem matrixHom_mem_cover (g : Model F) : matrixHom F e g ∈ Cover F := by
  have htop : (Cover F).comap (matrixHom F e) = ⊤ := by
    apply model_generates
    intro s k t
    change matrixHom F e (modelGenerator F s k t) ∈ Cover F
    rw [matrixHom_generator F e he]
    exact (coverSimple F s (pairNode 2 3 k) t).property
  exact (show g ∈ (Cover F).comap (matrixHom F e) by rw [htop]; trivial)

/-- Conditional construction of the faithful marked homomorphism into the cover. -/
def sourceModelOfChart : Model F →* Cover F :=
  (matrixHom F e).codRestrict (Cover F) (matrixHom_mem_cover F e he)

theorem sourceModelOfChart_injective : Function.Injective (sourceModelOfChart F e he) := by
  intro g h hgh
  exact matrixHom_injective F e (congrArg Subtype.val hgh)

@[simp] theorem sourceModelOfChart_generator (s k : Bool) (t : F) :
    sourceModelOfChart F e he (modelGenerator F s k t) =
      coverSimple F s (pairNode 2 3 k) t := by
  apply Subtype.ext
  exact matrixHom_generator F e he s k t

/-- Actual application to the literal pair subgroup, retaining its generators. -/
def pairLiftOfChart : pairSubgroup F 2 3 →* Model F :=
  pairModelLift F 2 3 (sourceModelOfChart F e he)
    (sourceModelOfChart_injective F e he) (modelGenerator F)
    (sourceModelOfChart_generator F e he)

@[simp] theorem pairLiftOfChart_generator (s k : Bool) (t : F) :
    pairLiftOfChart F e he (pairGenerator F 2 3 s k t) = modelGenerator F s k t :=
  pairModelLift_generator F 2 3 (sourceModelOfChart F e he)
    (sourceModelOfChart_injective F e he) (modelGenerator F)
    (sourceModelOfChart_generator F e he) s k t

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.ShortA2.SourceBlocks
