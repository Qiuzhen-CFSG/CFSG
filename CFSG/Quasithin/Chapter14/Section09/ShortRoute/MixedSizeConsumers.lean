module
public import CFSG.Quasithin.Chapter14.Section09.ShortRoute.MixedSize
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MixedZeroCore.DGSProfiles
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.At.Tensor

/-!
# The original mixed bound in the Chapter 10 and Theorem D consumers

The proved DGS numerical alternative supplies the exact MixedSizeInput with
no profile-exhaustion or Borel-recognition premise. Apply it to the literal
cubic-factor pair and its original Sylow, then to tensor-line centralization.
The independent cubic-factor construction remains explicit there.

The Chapter 14 tensor exclusion now discharges its mixed numerical premise.
It retains the original G,T, full KnownSimple catalogue and all earlier
structural and recognition hypotheses. This closes this numerical input;
the other DGS profiles and final classification assembly remain separate.
Source: Aschbacher--Smith F.1.12(I), 9.3.1 and 14.4.2(5),10--11,
printed pp.262--264,732--733,1006--1007,1010--1011.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
variable {G : Type*} [Group G] [Finite G]

/-- The exact original mixed-size contract, proved from F.1.1 and the two
literal quotient markings. The public contract retains all source premises. -/
theorem MixedZeroCore.mixedSizeInput_from_dgs_source : MixedZeroCore.MixedSizeInput G := by
  intro K U S h _ _ hK hU _
  exact ChapterF.Source.DGS85.ShortRoute.mixed_original_sylow_card_le h hK.some hU.some

namespace SourceA5TensorModel
open Chapter3.Section02 MixedZeroCore
variable {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- The actual cubic-factor pair has original Sylow order at most 256;
no profile or numerical premise remains. -/
theorem mixed_cubic_factor_source_sylow_bound
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B U : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hU : CubicFactor T A B U) (hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥) :
    Nat.card T ≤ 256 :=
  mixed_zero_core_sylow_bound mixedSizeInput_from_dgs_source hH eK A B U
    hAB hBA hBK hB3 hU hzero

/-- Original tensor-line centralization with its numerical DGS input discharged.
The independently constructed cubic factor remains the only mixed input. -/
theorem old_residual_centralizes_tensorLine_of_cubic_factor
    {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
    (m : SourceA5TensorModel D e) (factor : m.MixedCubicFactorInput)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < ChapterE.generationParameter H) :
    (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G) :=
  m.old_residual_centralizes_tensorLine_of_mixed_inputs mixedSizeInput_from_dgs_source factor hH hlarge

end SourceA5TensorModel
end CFSG.Quasithin.Chapter10

open Module Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Tensor LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- The same-G,T Theorem D tensor branch with the exact mixed-size theorem
supplied. Every earlier structural and full-catalogue hypothesis is retained. -/
theorem source_tensor_exclusion_from_dgs_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U) : False :=
  source_tensor_exclusion_of_mixed_size_at d earlier hq chosen structural alternatives
    classification Chapter10.MixedZeroCore.mixedSizeInput_from_dgs_source F hne hZ c

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
