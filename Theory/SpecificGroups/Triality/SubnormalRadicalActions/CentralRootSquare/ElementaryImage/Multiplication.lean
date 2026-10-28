module

public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.CentralRootSquare.ScalarObstruction

/-!
# Multiplication in the central triality radical

Collect the eleven supported D₄ root factors using the checked sum exchanges
and non-sum commutations. The first two cubic parameters add. The third gains
`higherCoefficient`, and the two fixed-field parameters gain the trace terms
specified in `multiply`. Every higher input parameter is retained.

The word calculation takes place in an abstract group, so only its final
identity is instantiated with the Geck curves. The published coordinate
and descent equivalences transport the result through the actual central
quotient. No restriction on q beyond characteristic two is used.

Source: GLS3 2.4.5(b)(4) and §2.6 (`refs/KGroup/GLS3/chapter2.tex`), with
the marking of `CentralHigherGeneration/Exchange.lean`; this is the central
radical in Aschbacher–Smith F.1.12(I)(4), printed pp.263–264.
-/

@[expose] public section
noncomputable section
open Triality.Standard.PositiveCoordinates
open Triality.Standard.PositiveCoordinates.SumExchangeData
open Triality.Standard.RadicalCoordinates
open Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.RadicalCoordinates.LeviCommutators
namespace Triality.Standard.Parabolics.CentralRootSquare.ElementaryImage

private theorem collect_sum {F G : Type*} [Mul F] [Group G]
    (x : Fin 12 → F → G)
    (hs : ∀ i j k, (i,j,k) ∈ sumTriples → ∀ a b,
      x i a * x j b = x j b * x i a * x k (a * b))
    (i j k : Fin 12) (h : (i,j,k) ∈ sumTriples) (a b : F) (g : G) :
    x i a * (x j b * g) = x j b * (x i a * (x k (a * b) * g)) := by
  rw [← mul_assoc, hs i j k h]
  simp only [mul_assoc]

private theorem collect_comm {F G : Type*} [Group G]
    (x : Fin 12 → F → G)
    (hc : ∀ i j, i ≠ j → (∀ k, (i,j,k) ∉ sumTriples) → ∀ a b,
      Commute (x i a) (x j b))
    (i j : Fin 12) (hij : i ≠ j) (h : ∀ k, (i,j,k) ∉ sumTriples)
    (a b : F) (g : G) :
    x i a * (x j b * g) = x j b * (x i a * g) := by
  rw [← mul_assoc, (hc i j hij h a b).eq, mul_assoc]

private theorem collect_add {F G : Type*} [Add F] [Group G]
    (x : Fin 12 → F → G) (ha : ∀ i a b, x i (a+b) = x i a * x i b)
    (i : Fin 12) (a b : F) (g : G) :
    x i a * (x i b * g) = x i (a+b) * g := by
  rw [← mul_assoc, ← ha]

private theorem central_collection {F G : Type*} [Add F] [Mul F] [Group G]
    (x : Fin 12 → F → G) (ha : ∀ i a b, x i (a+b) = x i a * x i b)
    (hs : ∀ i j k, (i,j,k) ∈ sumTriples → ∀ a b,
      x i a * x j b = x j b * x i a * x k (a*b))
    (hc : ∀ i j, i ≠ j → (∀ k, (i,j,k) ∉ sumTriples) → ∀ a b,
      Commute (x i a) (x j b))
    (v w : Fin 12 → F) :
    x 0 (v 0) * x 1 (v 1) * x 2 (v 2) * x 4 (v 4) * x 5 (v 5) * x 6 (v 6) * x 7 (v 7) * x 8 (v 8) * x 9 (v 9) * x 10 (v 10) * x 11 (v 11) *
      (x 0 (w 0) * x 1 (w 1) * x 2 (w 2) * x 4 (w 4) * x 5 (w 5) * x 6 (w 6) * x 7 (w 7) * x 8 (w 8) * x 9 (w 9) * x 10 (w 10) * x 11 (w 11)) =
      x 0 ((v 0) + (w 0)) *
      x 1 ((v 1) + (w 1)) *
      x 2 ((v 2) + (w 2)) *
      x 4 ((v 4) + (w 4)) *
      x 5 ((v 5) + (w 5)) *
      x 6 ((v 6) + (w 6)) *
      x 7 ((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) + (w 7)) *
      x 8 ((((v 5) * (w 2)) + (((v 6) * (w 1)) + (v 8))) + (w 8)) *
      x 9 ((((v 4) * (w 2)) + (((v 6) * (w 0)) + (v 9))) + (w 9)) *
      x 10 ((((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 2)) + (((((v 6) * (w 0)) + (v 9)) * (w 1)) + (((v 8) * (w 0)) + (v 10)))) + (w 10)) *
      x 11 ((((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 6)) + (((((v 4) * (w 2)) + (((v 6) * (w 0)) + (v 9))) * (w 5)) + (((((v 5) * (w 2)) + (((v 6) * (w 1)) + (v 8))) * (w 4)) + ((((v 4) * (w 2)) * (v 5)) + ((((v 4) * (w 1)) * (v 6)) + ((((v 5) * (w 0)) * (v 6)) + (v 11))))))) + (w 11)) := by
  suffices h :
      x 0 (v 0) * x 1 (v 1) * x 2 (v 2) * x 4 (v 4) * x 5 (v 5) * x 6 (v 6) * x 7 (v 7) * x 8 (v 8) * x 9 (v 9) * x 10 (v 10) * x 11 (v 11) *
      (x 0 (w 0) * x 1 (w 1) * x 2 (w 2) * x 4 (w 4) * x 5 (w 5) * x 6 (w 6) * x 7 (w 7) * x 8 (w 8) * x 9 (w 9) * x 10 (w 10) * x 11 (w 11)) * 1 =
      x 0 ((v 0) + (w 0)) *
      x 1 ((v 1) + (w 1)) *
      x 2 ((v 2) + (w 2)) *
      x 4 ((v 4) + (w 4)) *
      x 5 ((v 5) + (w 5)) *
      x 6 ((v 6) + (w 6)) *
      x 7 ((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) + (w 7)) *
      x 8 ((((v 5) * (w 2)) + (((v 6) * (w 1)) + (v 8))) + (w 8)) *
      x 9 ((((v 4) * (w 2)) + (((v 6) * (w 0)) + (v 9))) + (w 9)) *
      x 10 ((((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 2)) + (((((v 6) * (w 0)) + (v 9)) * (w 1)) + (((v 8) * (w 0)) + (v 10)))) + (w 10)) *
      x 11 ((((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 6)) + (((((v 4) * (w 2)) + (((v 6) * (w 0)) + (v 9))) * (w 5)) + (((((v 5) * (w 2)) + (((v 6) * (w 1)) + (v 8))) * (w 4)) + ((((v 4) * (w 2)) * (v 5)) + ((((v 4) * (w 1)) * (v 6)) + ((((v 5) * (w 0)) * (v 6)) + (v 11))))))) + (w 11)) * 1 by simpa only [mul_one] using h
  simp only [mul_assoc]
  conv_lhs =>
    rw [collect_comm x hc 11 0 (by decide) (by decide) (v 11) (w 0)]
    rw [collect_comm x hc 10 0 (by decide) (by decide) (v 10) (w 0)]
    rw [collect_comm x hc 9 0 (by decide) (by decide) (v 9) (w 0)]
    rw [collect_sum x hs 8 0 10 (by decide) (v 8) (w 0)]
    rw [collect_comm x hc 7 0 (by decide) (by decide) (v 7) (w 0)]
    rw [collect_sum x hs 6 0 9 (by decide) (v 6) (w 0)]
    rw [collect_sum x hs 5 0 7 (by decide) (v 5) (w 0)]
    rw [collect_comm x hc 4 0 (by decide) (by decide) (v 4) (w 0)]
    rw [collect_comm x hc 2 0 (by decide) (by decide) (v 2) (w 0)]
    rw [collect_comm x hc 1 0 (by decide) (by decide) (v 1) (w 0)]
    rw [collect_add x ha 0 (v 0) (w 0)]
    rw [collect_sum x hs 7 6 11 (by decide) ((v 5) * (w 0)) (v 6)]
    rw [collect_comm x hc 11 9 (by decide) (by decide) (((v 5) * (w 0)) * (v 6)) ((v 6) * (w 0))]
    rw [collect_comm x hc 11 7 (by decide) (by decide) (((v 5) * (w 0)) * (v 6)) (v 7)]
    rw [collect_comm x hc 9 7 (by decide) (by decide) ((v 6) * (w 0)) (v 7)]
    rw [collect_add x ha 7 ((v 5) * (w 0)) (v 7)]
    rw [collect_comm x hc 11 8 (by decide) (by decide) (((v 5) * (w 0)) * (v 6)) (v 8)]
    rw [collect_comm x hc 9 8 (by decide) (by decide) ((v 6) * (w 0)) (v 8)]
    rw [collect_comm x hc 11 10 (by decide) (by decide) (((v 5) * (w 0)) * (v 6)) ((v 8) * (w 0))]
    rw [collect_comm x hc 11 9 (by decide) (by decide) (((v 5) * (w 0)) * (v 6)) (v 9)]
    rw [collect_comm x hc 10 9 (by decide) (by decide) ((v 8) * (w 0)) (v 9)]
    rw [collect_add x ha 9 ((v 6) * (w 0)) (v 9)]
    rw [collect_comm x hc 11 10 (by decide) (by decide) (((v 5) * (w 0)) * (v 6)) (v 10)]
    rw [collect_add x ha 10 ((v 8) * (w 0)) (v 10)]
    rw [collect_add x ha 11 (((v 5) * (w 0)) * (v 6)) (v 11)]
    rw [collect_comm x hc 11 1 (by decide) (by decide) ((((v 5) * (w 0)) * (v 6)) + (v 11)) (w 1)]
    rw [collect_comm x hc 10 1 (by decide) (by decide) (((v 8) * (w 0)) + (v 10)) (w 1)]
    rw [collect_sum x hs 9 1 10 (by decide) (((v 6) * (w 0)) + (v 9)) (w 1)]
    rw [collect_comm x hc 8 1 (by decide) (by decide) (v 8) (w 1)]
    rw [collect_comm x hc 7 1 (by decide) (by decide) (((v 5) * (w 0)) + (v 7)) (w 1)]
    rw [collect_sum x hs 6 1 8 (by decide) (v 6) (w 1)]
    rw [collect_comm x hc 5 1 (by decide) (by decide) (v 5) (w 1)]
    rw [collect_sum x hs 4 1 7 (by decide) (v 4) (w 1)]
    rw [collect_comm x hc 2 1 (by decide) (by decide) (v 2) (w 1)]
    rw [collect_add x ha 1 (v 1) (w 1)]
    rw [collect_comm x hc 7 5 (by decide) (by decide) ((v 4) * (w 1)) (v 5)]
    rw [collect_sum x hs 7 6 11 (by decide) ((v 4) * (w 1)) (v 6)]
    rw [collect_comm x hc 11 8 (by decide) (by decide) (((v 4) * (w 1)) * (v 6)) ((v 6) * (w 1))]
    rw [collect_comm x hc 11 7 (by decide) (by decide) (((v 4) * (w 1)) * (v 6)) (((v 5) * (w 0)) + (v 7))]
    rw [collect_comm x hc 8 7 (by decide) (by decide) ((v 6) * (w 1)) (((v 5) * (w 0)) + (v 7))]
    rw [collect_add x ha 7 ((v 4) * (w 1)) (((v 5) * (w 0)) + (v 7))]
    rw [collect_comm x hc 11 8 (by decide) (by decide) (((v 4) * (w 1)) * (v 6)) (v 8)]
    rw [collect_add x ha 8 ((v 6) * (w 1)) (v 8)]
    rw [collect_comm x hc 11 9 (by decide) (by decide) (((v 4) * (w 1)) * (v 6)) (((v 6) * (w 0)) + (v 9))]
    rw [collect_comm x hc 11 10 (by decide) (by decide) (((v 4) * (w 1)) * (v 6)) ((((v 6) * (w 0)) + (v 9)) * (w 1))]
    rw [collect_comm x hc 11 10 (by decide) (by decide) (((v 4) * (w 1)) * (v 6)) (((v 8) * (w 0)) + (v 10))]
    rw [collect_add x ha 10 ((((v 6) * (w 0)) + (v 9)) * (w 1)) (((v 8) * (w 0)) + (v 10))]
    rw [collect_add x ha 11 (((v 4) * (w 1)) * (v 6)) ((((v 5) * (w 0)) * (v 6)) + (v 11))]
    rw [collect_comm x hc 11 2 (by decide) (by decide) ((((v 4) * (w 1)) * (v 6)) + ((((v 5) * (w 0)) * (v 6)) + (v 11))) (w 2)]
    rw [collect_comm x hc 10 2 (by decide) (by decide) (((((v 6) * (w 0)) + (v 9)) * (w 1)) + (((v 8) * (w 0)) + (v 10))) (w 2)]
    rw [collect_comm x hc 9 2 (by decide) (by decide) (((v 6) * (w 0)) + (v 9)) (w 2)]
    rw [collect_comm x hc 8 2 (by decide) (by decide) (((v 6) * (w 1)) + (v 8)) (w 2)]
    rw [collect_sum x hs 7 2 10 (by decide) (((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) (w 2)]
    rw [collect_comm x hc 6 2 (by decide) (by decide) (v 6) (w 2)]
    rw [collect_sum x hs 5 2 8 (by decide) (v 5) (w 2)]
    rw [collect_sum x hs 4 2 9 (by decide) (v 4) (w 2)]
    rw [collect_add x ha 2 (v 2) (w 2)]
    rw [collect_sum x hs 9 5 11 (by decide) ((v 4) * (w 2)) (v 5)]
    rw [collect_comm x hc 11 8 (by decide) (by decide) (((v 4) * (w 2)) * (v 5)) ((v 5) * (w 2))]
    rw [collect_comm x hc 9 8 (by decide) (by decide) ((v 4) * (w 2)) ((v 5) * (w 2))]
    rw [collect_comm x hc 11 6 (by decide) (by decide) (((v 4) * (w 2)) * (v 5)) (v 6)]
    rw [collect_comm x hc 9 6 (by decide) (by decide) ((v 4) * (w 2)) (v 6)]
    rw [collect_comm x hc 8 6 (by decide) (by decide) ((v 5) * (w 2)) (v 6)]
    rw [collect_comm x hc 11 7 (by decide) (by decide) (((v 4) * (w 2)) * (v 5)) (((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7)))]
    rw [collect_comm x hc 9 7 (by decide) (by decide) ((v 4) * (w 2)) (((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7)))]
    rw [collect_comm x hc 8 7 (by decide) (by decide) ((v 5) * (w 2)) (((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7)))]
    rw [collect_comm x hc 11 10 (by decide) (by decide) (((v 4) * (w 2)) * (v 5)) ((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 2))]
    rw [collect_comm x hc 11 8 (by decide) (by decide) (((v 4) * (w 2)) * (v 5)) (((v 6) * (w 1)) + (v 8))]
    rw [collect_comm x hc 10 8 (by decide) (by decide) ((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 2)) (((v 6) * (w 1)) + (v 8))]
    rw [collect_comm x hc 9 8 (by decide) (by decide) ((v 4) * (w 2)) (((v 6) * (w 1)) + (v 8))]
    rw [collect_add x ha 8 ((v 5) * (w 2)) (((v 6) * (w 1)) + (v 8))]
    rw [collect_comm x hc 11 9 (by decide) (by decide) (((v 4) * (w 2)) * (v 5)) (((v 6) * (w 0)) + (v 9))]
    rw [collect_comm x hc 10 9 (by decide) (by decide) ((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 2)) (((v 6) * (w 0)) + (v 9))]
    rw [collect_add x ha 9 ((v 4) * (w 2)) (((v 6) * (w 0)) + (v 9))]
    rw [collect_comm x hc 11 10 (by decide) (by decide) (((v 4) * (w 2)) * (v 5)) (((((v 6) * (w 0)) + (v 9)) * (w 1)) + (((v 8) * (w 0)) + (v 10)))]
    rw [collect_add x ha 10 ((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 2)) (((((v 6) * (w 0)) + (v 9)) * (w 1)) + (((v 8) * (w 0)) + (v 10)))]
    rw [collect_add x ha 11 (((v 4) * (w 2)) * (v 5)) ((((v 4) * (w 1)) * (v 6)) + ((((v 5) * (w 0)) * (v 6)) + (v 11)))]
    rw [collect_comm x hc 11 4 (by decide) (by decide) ((((v 4) * (w 2)) * (v 5)) + ((((v 4) * (w 1)) * (v 6)) + ((((v 5) * (w 0)) * (v 6)) + (v 11)))) (w 4)]
    rw [collect_comm x hc 10 4 (by decide) (by decide) (((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 2)) + (((((v 6) * (w 0)) + (v 9)) * (w 1)) + (((v 8) * (w 0)) + (v 10)))) (w 4)]
    rw [collect_comm x hc 9 4 (by decide) (by decide) (((v 4) * (w 2)) + (((v 6) * (w 0)) + (v 9))) (w 4)]
    rw [collect_sum x hs 8 4 11 (by decide) (((v 5) * (w 2)) + (((v 6) * (w 1)) + (v 8))) (w 4)]
    rw [collect_comm x hc 7 4 (by decide) (by decide) (((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) (w 4)]
    rw [collect_comm x hc 6 4 (by decide) (by decide) (v 6) (w 4)]
    rw [collect_comm x hc 5 4 (by decide) (by decide) (v 5) (w 4)]
    rw [collect_add x ha 4 (v 4) (w 4)]
    rw [collect_comm x hc 11 9 (by decide) (by decide) ((((v 5) * (w 2)) + (((v 6) * (w 1)) + (v 8))) * (w 4)) (((v 4) * (w 2)) + (((v 6) * (w 0)) + (v 9)))]
    rw [collect_comm x hc 11 10 (by decide) (by decide) ((((v 5) * (w 2)) + (((v 6) * (w 1)) + (v 8))) * (w 4)) (((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 2)) + (((((v 6) * (w 0)) + (v 9)) * (w 1)) + (((v 8) * (w 0)) + (v 10))))]
    rw [collect_add x ha 11 ((((v 5) * (w 2)) + (((v 6) * (w 1)) + (v 8))) * (w 4)) ((((v 4) * (w 2)) * (v 5)) + ((((v 4) * (w 1)) * (v 6)) + ((((v 5) * (w 0)) * (v 6)) + (v 11))))]
    rw [collect_comm x hc 11 5 (by decide) (by decide) (((((v 5) * (w 2)) + (((v 6) * (w 1)) + (v 8))) * (w 4)) + ((((v 4) * (w 2)) * (v 5)) + ((((v 4) * (w 1)) * (v 6)) + ((((v 5) * (w 0)) * (v 6)) + (v 11))))) (w 5)]
    rw [collect_comm x hc 10 5 (by decide) (by decide) (((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 2)) + (((((v 6) * (w 0)) + (v 9)) * (w 1)) + (((v 8) * (w 0)) + (v 10)))) (w 5)]
    rw [collect_sum x hs 9 5 11 (by decide) (((v 4) * (w 2)) + (((v 6) * (w 0)) + (v 9))) (w 5)]
    rw [collect_comm x hc 8 5 (by decide) (by decide) (((v 5) * (w 2)) + (((v 6) * (w 1)) + (v 8))) (w 5)]
    rw [collect_comm x hc 7 5 (by decide) (by decide) (((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) (w 5)]
    rw [collect_comm x hc 6 5 (by decide) (by decide) (v 6) (w 5)]
    rw [collect_add x ha 5 (v 5) (w 5)]
    rw [collect_comm x hc 11 10 (by decide) (by decide) ((((v 4) * (w 2)) + (((v 6) * (w 0)) + (v 9))) * (w 5)) (((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 2)) + (((((v 6) * (w 0)) + (v 9)) * (w 1)) + (((v 8) * (w 0)) + (v 10))))]
    rw [collect_add x ha 11 ((((v 4) * (w 2)) + (((v 6) * (w 0)) + (v 9))) * (w 5)) (((((v 5) * (w 2)) + (((v 6) * (w 1)) + (v 8))) * (w 4)) + ((((v 4) * (w 2)) * (v 5)) + ((((v 4) * (w 1)) * (v 6)) + ((((v 5) * (w 0)) * (v 6)) + (v 11)))))]
    rw [collect_comm x hc 11 6 (by decide) (by decide) (((((v 4) * (w 2)) + (((v 6) * (w 0)) + (v 9))) * (w 5)) + (((((v 5) * (w 2)) + (((v 6) * (w 1)) + (v 8))) * (w 4)) + ((((v 4) * (w 2)) * (v 5)) + ((((v 4) * (w 1)) * (v 6)) + ((((v 5) * (w 0)) * (v 6)) + (v 11)))))) (w 6)]
    rw [collect_comm x hc 10 6 (by decide) (by decide) (((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 2)) + (((((v 6) * (w 0)) + (v 9)) * (w 1)) + (((v 8) * (w 0)) + (v 10)))) (w 6)]
    rw [collect_comm x hc 9 6 (by decide) (by decide) (((v 4) * (w 2)) + (((v 6) * (w 0)) + (v 9))) (w 6)]
    rw [collect_comm x hc 8 6 (by decide) (by decide) (((v 5) * (w 2)) + (((v 6) * (w 1)) + (v 8))) (w 6)]
    rw [collect_sum x hs 7 6 11 (by decide) (((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) (w 6)]
    rw [collect_add x ha 6 (v 6) (w 6)]
    rw [collect_comm x hc 11 8 (by decide) (by decide) ((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 6)) (((v 5) * (w 2)) + (((v 6) * (w 1)) + (v 8)))]
    rw [collect_comm x hc 11 9 (by decide) (by decide) ((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 6)) (((v 4) * (w 2)) + (((v 6) * (w 0)) + (v 9)))]
    rw [collect_comm x hc 11 10 (by decide) (by decide) ((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 6)) (((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 2)) + (((((v 6) * (w 0)) + (v 9)) * (w 1)) + (((v 8) * (w 0)) + (v 10))))]
    rw [collect_add x ha 11 ((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 6)) (((((v 4) * (w 2)) + (((v 6) * (w 0)) + (v 9))) * (w 5)) + (((((v 5) * (w 2)) + (((v 6) * (w 1)) + (v 8))) * (w 4)) + ((((v 4) * (w 2)) * (v 5)) + ((((v 4) * (w 1)) * (v 6)) + ((((v 5) * (w 0)) * (v 6)) + (v 11))))))]
    rw [collect_comm x hc 11 7 (by decide) (by decide) (((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 6)) + (((((v 4) * (w 2)) + (((v 6) * (w 0)) + (v 9))) * (w 5)) + (((((v 5) * (w 2)) + (((v 6) * (w 1)) + (v 8))) * (w 4)) + ((((v 4) * (w 2)) * (v 5)) + ((((v 4) * (w 1)) * (v 6)) + ((((v 5) * (w 0)) * (v 6)) + (v 11))))))) (w 7)]
    rw [collect_comm x hc 10 7 (by decide) (by decide) (((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 2)) + (((((v 6) * (w 0)) + (v 9)) * (w 1)) + (((v 8) * (w 0)) + (v 10)))) (w 7)]
    rw [collect_comm x hc 9 7 (by decide) (by decide) (((v 4) * (w 2)) + (((v 6) * (w 0)) + (v 9))) (w 7)]
    rw [collect_comm x hc 8 7 (by decide) (by decide) (((v 5) * (w 2)) + (((v 6) * (w 1)) + (v 8))) (w 7)]
    rw [collect_add x ha 7 (((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) (w 7)]
    rw [collect_comm x hc 11 8 (by decide) (by decide) (((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 6)) + (((((v 4) * (w 2)) + (((v 6) * (w 0)) + (v 9))) * (w 5)) + (((((v 5) * (w 2)) + (((v 6) * (w 1)) + (v 8))) * (w 4)) + ((((v 4) * (w 2)) * (v 5)) + ((((v 4) * (w 1)) * (v 6)) + ((((v 5) * (w 0)) * (v 6)) + (v 11))))))) (w 8)]
    rw [collect_comm x hc 10 8 (by decide) (by decide) (((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 2)) + (((((v 6) * (w 0)) + (v 9)) * (w 1)) + (((v 8) * (w 0)) + (v 10)))) (w 8)]
    rw [collect_comm x hc 9 8 (by decide) (by decide) (((v 4) * (w 2)) + (((v 6) * (w 0)) + (v 9))) (w 8)]
    rw [collect_add x ha 8 (((v 5) * (w 2)) + (((v 6) * (w 1)) + (v 8))) (w 8)]
    rw [collect_comm x hc 11 9 (by decide) (by decide) (((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 6)) + (((((v 4) * (w 2)) + (((v 6) * (w 0)) + (v 9))) * (w 5)) + (((((v 5) * (w 2)) + (((v 6) * (w 1)) + (v 8))) * (w 4)) + ((((v 4) * (w 2)) * (v 5)) + ((((v 4) * (w 1)) * (v 6)) + ((((v 5) * (w 0)) * (v 6)) + (v 11))))))) (w 9)]
    rw [collect_comm x hc 10 9 (by decide) (by decide) (((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 2)) + (((((v 6) * (w 0)) + (v 9)) * (w 1)) + (((v 8) * (w 0)) + (v 10)))) (w 9)]
    rw [collect_add x ha 9 (((v 4) * (w 2)) + (((v 6) * (w 0)) + (v 9))) (w 9)]
    rw [collect_comm x hc 11 10 (by decide) (by decide) (((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 6)) + (((((v 4) * (w 2)) + (((v 6) * (w 0)) + (v 9))) * (w 5)) + (((((v 5) * (w 2)) + (((v 6) * (w 1)) + (v 8))) * (w 4)) + ((((v 4) * (w 2)) * (v 5)) + ((((v 4) * (w 1)) * (v 6)) + ((((v 5) * (w 0)) * (v 6)) + (v 11))))))) (w 10)]
    rw [collect_add x ha 10 (((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 2)) + (((((v 6) * (w 0)) + (v 9)) * (w 1)) + (((v 8) * (w 0)) + (v 10)))) (w 10)]
    rw [collect_add x ha 11 (((((v 4) * (w 1)) + (((v 5) * (w 0)) + (v 7))) * (w 6)) + (((((v 4) * (w 2)) + (((v 6) * (w 0)) + (v 9))) * (w 5)) + (((((v 5) * (w 2)) + (((v 6) * (w 1)) + (v 8))) * (w 4)) + ((((v 4) * (w 2)) * (v 5)) + ((((v 4) * (w 1)) * (v 6)) + ((((v 5) * (w 0)) * (v 6)) + (v 11))))))) (w 11)]

/-- The full central-radical collecting law, retaining both singleton coordinates. -/
def multiply (P : Parameters) (v w : RootOrbitParameters P .central) :
    RootOrbitParameters P .central :=
  (![v.1 0 + w.1 0, v.1 1 + w.1 1,
      v.1 2 + w.1 2 + higherCoefficient P (w.1 0) (v.1 1)],
    ![v.2 0 + w.2 0 + armsPairing P (w.1 0) (v.1 2) +
        cubicTrace P (v.1 1 * fieldFrobenius P (w.1 0) *
          fieldFrobenius P (fieldFrobenius P (w.1 0))),
      v.2 1 + w.2 1 + armsPairing P (w.1 1) (v.1 2) +
        cubicTrace P (w.1 0 * fieldFrobenius P (v.1 1) *
          fieldFrobenius P (fieldFrobenius P (v.1 1))) +
        armsPairing P (w.1 1) (higherCoefficient P (w.1 0) (v.1 1))])

private theorem folded_multiply (P : Parameters) {G : Type*} [Group G]
    (x : Fin 12 → ExtensionField P → G)
    (hz : ∀ i, x i 0 = 1)
    (ha : ∀ i a b, x i (a+b) = x i a * x i b)
    (hs : ∀ i j k, (i,j,k) ∈ sumTriples → ∀ a b,
      x i a * x j b = x j b * x i a * x k (a*b))
    (hc : ∀ i j, i ≠ j → (∀ k, (i,j,k) ∉ sumTriples) → ∀ a b,
      Commute (x i a) (x j b))
    (v w : RootOrbitParameters P .central) :
    (List.ofFn (fun i => x i (expand P (extendOrbit P .central (multiply P v w)) i))).prod =
      (List.ofFn (fun i => x i (expand P (extendOrbit P .central v) i))).prod *
      (List.ofFn (fun i => x i (expand P (extendOrbit P .central w) i))).prod := by
  have he := central_collection x ha hs hc
    (expand P (extendOrbit P .central v)) (expand P (extendOrbit P .central w))
  simp [expand, extendOrbit, List.ofFn_succ, hz, -fieldFrobenius_apply] at he ⊢
  simp only [mul_assoc] at he ⊢
  rw [he]
  simp [multiply, armsPairing_coe, cubicTrace_coe,
    higherCoefficient, map_mul, fieldFrobenius_three, -fieldFrobenius_apply]
  congr 1 <;> ring_nf

private theorem product_multiply (P : Parameters) (hp : P.prime = 2)
    (v w : RootOrbitParameters P .central) :
    orderedProduct P (expand P (extendOrbit P .central (multiply P v w))) =
      orderedProduct P (expand P (extendOrbit P .central v)) *
      orderedProduct P (expand P (extendOrbit P .central w)) := by
  have hs : SumExchange P := by
    obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
    exact sumExchange_binary n hn
  exact folded_multiply P (curve P) (curve_zero P) (curve_add P)
    (fun i j k h => hs i j k ((root_sum_iff i j k).mpr ((mem_sumTriples_iff i j k).mp h)))
    (fun i j hij h => nonsumCommute_parameters P i j hij (by
      rintro ⟨k, hk⟩
      exact h k ((mem_sumTriples_iff i j k).mpr ((root_sum_iff i j k).mp hk)))) v w

theorem coordinates_multiply (P : Parameters) (hp : P.prime = 2)
    (v w : RootOrbitParameters P .central) :
    coordinates P hp (multiply P v w) = coordinates P hp v * coordinates P hp w := by
  let f : RootOrbitParameters P .central →
      (rootSubgroup P .central).comap (fixedSubgroup P).subtype :=
    fun v => fixedRootEquiv P hp .central (rootOrbitEquiv P .central v)
  have h : f (multiply P v w) = f v * f w :=
    Subtype.ext (Subtype.ext (product_multiply P hp v w))
  let e := (descendedRootEquiv P hp .central).trans
    (MulEquiv.subgroupCongr (radical_eq_descendedRootSubgroup P hp .central).symm)
  exact (congrArg e h).trans (e.map_mul (f v) (f w))

end Triality.Standard.Parabolics.CentralRootSquare.ElementaryImage
