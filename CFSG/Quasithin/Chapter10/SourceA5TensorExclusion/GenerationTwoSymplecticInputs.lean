module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoAssembly
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic

/-!
# Independent inputs for the original symplectic tensor branch

The marking in the generation-two data is on the action image of the literal
Omega orbit. Applying rank-two pushing up requires a separate identification
of its centralizer with the two-core. Whole-block recognition and restriction
to the original plane parabolic are subsequent, independent arguments.

These are source contracts, not conclusions asserted by the tensor model.
GenerationTwoSymplecticKernel proves the first contract from the actual action
marking. Whole-block recognition and the original marked-plane construction
remain with qt-d-tensor-sp4-plane; their conditional interfaces stay explicit.

Source: Aschbacher--Smith 9.3.10 and the final paragraph of 9.3, printed
pp.734--735; C.1.32 and Meierfrankenfeld--Stellmacher (1993), (3.6).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- Identify the original action kernel before using a two-core quotient model. -/
@[expose] def SymplecticKernelRecognition : Prop :=
  ∀ c : m.GenerationTwoOvergroup,
    let W := omegaOrbit (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ hr : IsPReduced 2 W,
      letI := hr.normal
      Nonempty (((pResidual 2 c.M).map (actionMk W)) ≃*
        Matrix.symplecticGroup (Fin 2) ChapterB.QuasisimpleSource.BinaryField.four.Carrier) →
      centralizer (W : Set c.M) = pCore 2 c.M

/-- Whole intrinsic block recognition; a quotient marking alone is not a block. -/
@[expose] def SymplecticBlockRecognition : Prop :=
  ∀ c : m.GenerationTwoOvergroup,
    ((pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Matrix.symplecticGroup (Fin 2) ChapterB.QuasisimpleSource.BinaryField.four.Carrier) →
    ChapterC.IsSp4FourBlock (pResidual 2 c.M)

/-- Restrict the whole block to the original component, retaining the literal
plane-local surjection and full-module quotient required by `Placement`. -/
@[expose] def SymplecticPlaneFromBlock : Prop :=
  ∀ c : m.GenerationTwoOvergroup,
    ((pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Matrix.symplecticGroup (Fin 2) ChapterB.QuasisimpleSource.BinaryField.four.Carrier) →
    ChapterC.IsSp4FourBlock (pResidual 2 c.M) → Nonempty (OriginalPlaneModel D)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
