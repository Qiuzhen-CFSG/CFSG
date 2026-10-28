module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Estimate
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords.Exchange
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords.GraphModels
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords.OuterModels

/-!
# Displacement and source application for adjoint tensor operators

Transpose on one trace-zero factor moves at least a quarter of the full tensor
space, regardless of the residual operator. Interchange on a nontrivial tensor
square has the same bound. Transport through the literal Schur scalar extension
preserves the ratio exactly. The existing 32r degree gap then excludes the
original elementary cubic actor.

The graph and outer-type producers construct these literal operator models
from the central-kernel hypothesis. Their assembly proves the displacement
bound and its common-fixed-space application with no extra model premise.
Source: GM, Classification of 2F-modules II, Proposition 4.8 steps 2–5,
manuscript pp.26–28; Aschbacher–Smith K.3.2, printed pp.454–456.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Representation Representation.BinaryOffender
open Representation.BinaryOffender.SchurNormalizer
open Representation.SL3.BinaryDefiningFactors
open Representation.SL3.BinaryDefiningFactors.AdjointTensorTranspose
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open LinearMap.FixedSpaceTransport
open scoped MatrixGroups TensorProduct

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors
namespace AdjointWords
variable {B : BinaryField} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {σ : Representation (ZMod 2) SL(3,B.Carrier) V} [IsIrreducible σ]
    {t : linearNormalizer σ} {hs : IsSchurLinear σ t}

private theorem displacement_of_model
    {W : Type*} [AddCommGroup W] [Module (SplittingField σ) W]
    [FiniteDimensional (SplittingField σ) W]
    (e : (SplittingField σ ⊗[SchurField σ] σ.asModule) ≃ₗ[SplittingField σ] W)
    (f : Module.End (SplittingField σ) W)
    (he : ∀ v, e (absoluteActor σ (SplittingField σ) t hs v) = f (e v))
    (hf : Module.finrank (SplittingField σ) W ≤
      4 * Module.finrank (SplittingField σ) (f - 1).range) :
    Module.finrank (ZMod 2) V ≤ 4 * Module.finrank (ZMod 2) (t.val.val - 1).range := by
  have hr := finrank_range_sub_one_equiv e
    (absoluteActor σ (SplittingField σ) t hs) f he
  have hb := binary_range_finrank σ (SplittingField σ) t hs
  rw [hr] at hb
  have hd := Representation.finrank_eq_schurDegree_mul 2 σ (SplittingField σ)
  rw [e.finrank_eq] at hd
  have hbound := Nat.mul_le_mul_left (Representation.schurDegree 2 σ) hf
  rw [← hd] at hbound
  rw [hb]
  simpa only [Nat.mul_left_comm] using hbound

local instance : AddCommGroup (AdjointSpace (SplittingField σ)) := inferInstance

/-- The graph tensor bound descends through the original Schur field. -/
theorem GraphRealization.displacement (R : GraphRealization B σ t hs) :
    Module.finrank (ZMod 2) V ≤ 4 * Module.finrank (ZMod 2) (t.val.val - 1).range :=
  displacement_of_model R.equiv (graphTensor R.residual) R.action
    (graph_tensor_displacement R.residual)

/-- Exact tensor interchange, including the smallest nontrivial square,
satisfies the same quarter-displacement estimate. -/
theorem ExchangeRealization.displacement (R : ExchangeRealization B σ t hs) :
    Module.finrank (ZMod 2) V ≤ 4 * Module.finrank (ZMod 2) (t.val.val - 1).range := by
  have he := finrank_range_sub_one_equiv R.equiv
    (absoluteActor σ (SplittingField σ) t hs)
    (TensorInterchange.flip (SplittingField σ) R.size) R.action
  have hb := binary_range_finrank σ (SplittingField σ) t hs
  rw [he, TensorInterchange.finrank_range_flip] at hb
  have hd := Representation.finrank_eq_schurDegree_mul 2 σ (SplittingField σ)
  rw [R.equiv.finrank_eq, TensorInterchange.finrank_space] at hd
  have hchoose : 2 * R.size.choose 2 + R.size = R.size * R.size := by
    have h (n : ℕ) : 2 * n.choose 2 + n = n * n := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
        nlinarith
    exact h R.size
  have hbound : R.size * R.size ≤ 4 * R.size.choose 2 := by
    have := Nat.mul_le_mul_left R.size R.two_le
    nlinarith
  have hm := Nat.mul_le_mul_left (Representation.schurDegree 2 σ) hbound
  rw [hd, hb]
  simpa only [Nat.mul_left_comm] using hm

/-- Paired component coordinates suffice for displacement on the original
binary operator. No fixed-space or displacement hypothesis is supplied. -/
theorem displacement_of_pairedCoordinates
    (L : Realization.LiftedInvolution B σ t)
    (ht : IsSchurLinear σ t)
    (P : Realization.PairedTensorCoordinates B σ L.automorphism) :
    Module.finrank (ZMod 2) V ≤ 4 * Module.finrank (ZMod 2) (t.val.val - 1).range :=
  (exchangeRealization_of_pairedCoordinates L ht P).displacement
end AdjointWords

variable {B : BinaryField} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {σ : Representation (ZMod 2) SL(3,B.Carrier) V} [IsIrreducible σ]

/-- Assembly of the two actual operator-model constructions. -/
theorem adjointTensorDisplacement_of_models
    (hg : AdjointWords.GraphModels B σ) (ho : AdjointWords.OuterModels B σ) :
    AdjointTensorDisplacement B σ := by
  intro M ha hb hj t h2 ht hs
  rcases ho M ha hb hj t h2 ht hs with hgraph | hswap
  · obtain ⟨R⟩ := hg M ha hb hj t h2 ht hs hgraph
    exact R.displacement
  · obtain ⟨R⟩ := hswap
    exact R.displacement

/-- Application to the literal original actor and its common fixed space.
The graph and field model premises still require their geometric producers. -/
theorem adjointTensorEstimate_of_models
    (hg : AdjointWords.GraphModels B σ) (ho : AdjointWords.OuterModels B σ) :
    AdjointTensorEstimate B σ :=
  adjointTensorEstimate_of_displacement (adjointTensorDisplacement_of_models hg ho)

/-- Every Schur-linear outer involution moves at least one quarter of the
original binary module on the remaining pure-adjoint repeated words.
The actual graph and exchange models are constructed from the central kernel. -/
theorem adjointTensorDisplacement (hk : σ.ker ≤ Subgroup.center _) :
    AdjointTensorDisplacement B σ :=
  adjointTensorDisplacement_of_models
    (AdjointWords.graph_models hk) (AdjointWords.outer_models hk)

/-- The resulting strict estimate for the original elementary cubic actor's
common fixed space. The 32r degree gap and the supplied actor rank bound
discharge the numerical comparison; no operator-model premise remains. -/
theorem adjointTensorEstimate (hk : σ.ker ≤ Subgroup.center _) :
    AdjointTensorEstimate B σ :=
  adjointTensorEstimate_of_displacement (adjointTensorDisplacement hk)

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors
