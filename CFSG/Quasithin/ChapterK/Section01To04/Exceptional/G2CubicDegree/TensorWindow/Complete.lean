module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.CoarseBound
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.HalfTensor
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree

/-!
# The G₂ cubic tensor degree window

A faithful irreducible binary G₂(2ʳ)-module with a threshold-two cubic actor
in its actual linear normalizer has degree strictly below `18*r`, given the
explicit automorphism two-rank bound `3*r`.

Threshold-two maximization first bounds the degree by `34*r`. Frobenius
descent leaves only degree `18*r` above the desired window. At this degree,
the actor is linear over the actual Schur field, and the recognized pair of
natural factors gives involution displacement at least `5/12` of the binary
degree, contradicting the actor's upper bound `6*r`. This includes the outer
factor-exchange case.

The first theorem discharges the literal `hwindow` premise of
`degree_lt_of_cubic_estimates`. The second applies that consumer, retaining
only its independent adjoint obstruction and the explicit rank hypothesis.
Their discharge belongs to the parent G₂ cubic-degree assembly.

Source: Guralnick–Malle, Classification of 2F-modules II, §3.5 equations
(3.3)–(3.5), manuscript p.20, and Lemma 8.5, pp.55–56; used in
Aschbacher–Smith K.3, printed p.457. See `G2CubicDegree/Source.md`.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree
open Representation Representation.BinaryOffender
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterG.Section09
attribute [local instance] ZMod.algebra

variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (σ : Representation (ZMod 2) (Atlas.G2.Model F) V) [IsIrreducible σ]

/-- The full tensor window, with every representation estimate discharged.
Only the explicitly supplied automorphism two-rank bound is retained. -/
theorem TensorWindow.degree_lt_of_cubic_actor
    {r : ℕ} (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r)
    (hf : Function.Injective σ)
    (hAut : primeRank 2 (MulAut (Atlas.G2.Model F)) ≤ 3 * r)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hcube : IsCubic (normalizerRepresentation σ) A)
    (hsmall : fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A) :
    Module.finrank (ZMod 2) V < 18 * r :=
  TensorWindow.window_of_coarse_and_half_tensor_estimates σ hr hF hf hAut
    (TensorWindow.degree_lt_thirtyFour_of_small_actor σ hr hF hf hAut)
    (TensorWindow.HalfTensor.bound σ hr hF hf) A hA hcube hsmall

/-- The literal cubic-degree consumer with its tensor-window premise proved.
The adjoint common-fixed-space obstruction remains an independent input. -/
theorem degree_lt_of_adjoint_estimate
    {r : ℕ} (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r)
    (hf : Function.Injective σ) (hc : cubicRatio (normalizerRepresentation σ) ≤ 2)
    (hAut : primeRank 2 (MulAut (Atlas.G2.Model F)) ≤ 3 * r)
    (hadjoint : Quasiequivalent σ (adjointBinary F) →
      ∀ A : Subgroup (linearNormalizer σ),
      IsElementaryTwo A → IsCubic (normalizerRepresentation σ) A →
      2 * rank A < fixedCodim (normalizerRepresentation σ) A) :
    Module.finrank (ZMod 2) V < 14 * r :=
  degree_lt_of_cubic_estimates σ hr hF hf hc
    (TensorWindow.degree_lt_of_cubic_actor σ hr hF hf hAut) hadjoint

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree
