module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.EvenTwisted.Triality.Inputs
public import Theory.Representation.Triality.OuterDisplacement.Commutant
public import Theory.Representation.Triality.OuterDisplacement.Degree
public import Theory.Representation.Triality.OuterDisplacement.TensorCoordinates
import Mathlib.Tactic

/-!
# Outer triality displacement: commutants and paired factors

The genuine central quotient gives binary degree at least 12*n through every
central cover. An operator moving a component endomorphism displaces at least
half the module by Schur's lemma. This settles that branch even when the
component restriction is not absolutely irreducible.

For operators centralizing the component commutant, actual paired tensor
coordinates give displacement at least 7/16 of the dimension, hence strictly
more than 5*n binary dimensions. The coordinates must intertwine the literal
ambient operator after scalar extension. Their existence is the remaining
source input, and the final theorem is explicitly conditional on it. No
unconditional even-exponent outer bound is asserted by this module.

Source: Guralnick--Malle, *Classification of 2F-modules, II*, Proposition 2.5,
Section 3.5 and Lemma 8.6, internal pp.6, 20, 56--57. See `EvenTwisted/Source.md`.
The even-exponent source assembly retains normality, quasisimplicity, F*(H)=N,
and the original central quotient; the linear estimates below need fewer
hypotheses.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality

open Representation
open _root_.Triality.OuterDisplacement

universe u v

variable {H : Type u} [Group H] [Finite H] (N : Subgroup H)

/-- The actual central quotient gives degree at least 12*n, so the paired
factor displacement ratio already exceeds the automorphism rank 5*n. -/
theorem displacement_gt_of_ratio {E W : Type v} [Field E] [Finite E]
    [Algebra (ZMod 2) E] [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (σ : Representation E H W) (hσ : Function.Injective σ)
    (n : ℕ) (hn : 0 < n)
    (hmodel : _root_.Triality.Standard.IsTrialityGroupAt (2 ^ n) (N ⧸ Subgroup.center N))
    (t : H)
    (hratio : 7 * Module.finrank E W ≤
      16 * Module.finrank E (LinearMap.range (σ t - LinearMap.id))) :
    5 * n < Module.finrank (ZMod 2) E *
      Module.finrank E (LinearMap.range (σ t - LinearMap.id)) := by
  have hd := degree_ge_of_central_quotient σ hσ N n hn hmodel
  have hr := Nat.mul_le_mul_left (Module.finrank (ZMod 2) E) hratio
  nlinarith

/-- The outer-operator branch moving the component commutant is discharged
without a representation classification or absolute component irreducibility. -/
theorem displacement_gt_of_not_centralizesCommutant [N.Normal]
    {E W : Type v} [Field E] [Finite E] [Algebra (ZMod 2) E]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (σ : Representation E H W) [IsIrreducible (σ.comp N.subtype)]
    (hσ : Function.Injective σ) (n : ℕ) (hn : 0 < n)
    (hmodel : _root_.Triality.Standard.IsTrialityGroupAt (2 ^ n) (N ⧸ Subgroup.center N))
    (t : H) (ht : ¬ CentralizesCommutant σ N t) :
    5 * n < Module.finrank (ZMod 2) E *
      Module.finrank E (LinearMap.range (σ t - LinearMap.id)) := by
  apply displacement_gt_of_ratio N σ hσ n hn hmodel t
  have hd := finrank_le_twice_displacement_of_not_centralizesCommutant σ N t ht
  omega

/-- Apply the tensor estimate to the original ambient representation operator. -/
theorem displacement_gt_of_pairedTensorCoordinates
    {E W : Type v} [Field E] [Finite E] [Algebra (ZMod 2) E]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (σ : Representation E H W) (hσ : Function.Injective σ) (n : ℕ) (hn : 0 < n)
    (hmodel : _root_.Triality.Standard.IsTrialityGroupAt (2 ^ n) (N ⧸ Subgroup.center N))
    (t : H) (ht : HasPairedTensorCoordinates (σ t)) :
    5 * n < Module.finrank (ZMod 2) E *
      Module.finrank E (LinearMap.range (σ t - LinearMap.id)) :=
  displacement_gt_of_ratio N σ hσ n hn hmodel t
    (displacement_ratio_of_pairedTensorCoordinates (σ t) ht)

/-- Conditional outer-bound assembly. Only operators centralizing the entire
component commutant need a paired tensor realization. Its construction remains
an explicit prerequisite; this theorem does not assert the source estimate. -/
theorem outerInvolutionBound_of_pairedTensorCoordinates [N.Normal]
    (n : ℕ) (hn : 0 < n)
    (hmodel : _root_.Triality.Standard.IsTrialityGroupAt (2 ^ n) (N ⧸ Subgroup.center N))
    (hpaired : ∀ (E W : Type v) [Field E] [Finite E] [Algebra (ZMod 2) E] [CharP E 2]
      [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (σ : Representation E H W),
      IsAbsolutelyIrreducible σ → IsIrreducible (σ.comp N.subtype) →
      Function.Injective σ → ∀ t : H, t ∉ N → t ^ 2 = 1 →
      CentralizesCommutant σ N t → HasPairedTensorCoordinates (σ t)) :
    OuterInvolutionBound.{u, v} H N n := by
  classical
  intro E W _ _ _ _ _ _ _ σ habs hirr hσ t ht ht2
  let : IsIrreducible (σ.comp N.subtype) := hirr
  by_cases hc : CentralizesCommutant σ N t
  · exact displacement_gt_of_pairedTensorCoordinates N σ hσ n hn hmodel t
      (hpaired E W σ habs hirr hσ t ht ht2 hc)
  · exact displacement_gt_of_not_centralizesCommutant N σ hσ n hn hmodel t hc

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality
