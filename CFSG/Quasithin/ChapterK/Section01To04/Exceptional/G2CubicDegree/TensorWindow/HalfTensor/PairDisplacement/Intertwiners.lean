module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.HalfTensor.Model
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.HalfTensor.Swap
public import Theory.Representation.TensorInvolutionIntertwiners

/-!
# Intertwiner rigidity on the concrete natural G₂ pair

The induced group automorphism is retained literally. For an inner square-one
representative, Schur rigidity identifies its pair action with the given
involution. For a representative exchanging the two actual natural factors,
Schur rigidity gives a scalar multiple of that exchange. The involution equation
normalizes its second factor to the inverse of its first, and the twisted-swap
calculation gives displacement at least fifteen.

Existence of the inner or exchange representative is a separate structural
obligation. This module proves the consequences without assuming scalar
normalization or any displacement estimate for an exchange representative.

Source: Guralnick–Malle, Classification of 2F-modules II, §3.5 and Lemma 8.5,
manuscript pp.20,55–56; see `G2CubicDegree/Source.md`.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct

namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow.HalfTensor
open Representation.BinaryOffender.NaturalTensor
open Representation.TensorInvolutionIntertwiners
variable (F K : Type*) [Field F] [CharP F 2] [Field K] [Algebra F K]

/-- The literal exchange with a linear map on each natural scalar factor. -/
@[expose] def pairExchange (f g : NaturalScalarSpace F K ≃ₗ[K] NaturalScalarSpace F K) :
    PairSpace F K ≃ₗ[K] PairSpace F K :=
  (TensorProduct.comm K _ _).trans (TensorProduct.congr f g)

@[simp] theorem pairExchange_tmul
    (f g : NaturalScalarSpace F K ≃ₗ[K] NaturalScalarSpace F K)
    (x y : NaturalScalarSpace F K) :
    pairExchange F K f g (x ⊗ₜ[K] y) = f y ⊗ₜ[K] g x := rfl

variable [Finite F] [CharP K 2] [IsAlgClosed K] (i s : ℕ)
  [Representation.IsIrreducible (k := K) (G := Atlas.G2.Model F)
    (V := PairSpace F K) (pairRep F K i s)]

/-- An involutory intertwiner with an exchange representative moves at least fifteen dimensions. -/
theorem pair_exchange_intertwiner_displacement
    (T : Module.End K (PairSpace F K)) (α : MulAut (Atlas.G2.Model F))
    (hT2 : T * T = 1)
    (hT : ∀ h, T * pairRep F K i s h = pairRep F K i s (α h) * T)
    (f g : NaturalScalarSpace F K ≃ₗ[K] NaturalScalarSpace F K)
    (hS : ∀ h, (pairExchange F K f g).toLinearMap * pairRep F K i s h =
      pairRep F K i s (α h) * (pairExchange F K f g).toLinearMap) :
    15 ≤ operatorFixedCodim (k := K) (V := PairSpace F K) T := by
  obtain ⟨c, hc⟩ := same_automorphism_scalar (K := K) (U := PairSpace F K) (pairRep F K i s) α T
    (pairExchange F K f g) hT hS
  apply pair_twisted_swap_displacement F K f T
  apply normalize_exchange f g c T hT2
  intro x y
  rw [hc]
  rfl

/-- An inner involutory representative is the original intertwiner, with no scalar ambiguity. -/
theorem pair_inner_intertwiner_eq
    (T : Module.End K (PairSpace F K)) (α : MulAut (Atlas.G2.Model F))
    (hT2 : T * T = 1)
    (hT : ∀ h, T * pairRep F K i s h = pairRep F K i s (α h) * T)
    (g : Atlas.G2.Model F) (hg : g * g = 1) (hα : α = MulAut.conj g) :
    T = pairRep F K i s g := by
  let ρ := pairRep F K i s
  have hρ2 : ρ g * ρ g = 1 := by rw [← map_mul, hg, map_one]
  let S : PairSpace F K ≃ₗ[K] PairSpace F K :=
    { toLinearMap := ρ g
      invFun := ρ g
      left_inv := fun v => congrArg (fun A : Module.End K (PairSpace F K) => A v) hρ2
      right_inv := fun v => congrArg (fun A : Module.End K (PairSpace F K) => A v) hρ2 }
  let : Nontrivial (PairSpace F K) := Module.nontrivial_of_finrank_pos (R := K)
    (by rw [finrank_pairSpace]; omega)
  apply same_automorphism_involutions_eq (K := K) (U := PairSpace F K) ρ α T S hT _ hT2 hρ2
  intro h
  change ρ g * ρ h = ρ (α h) * ρ g
  rw [← map_mul, ← map_mul]
  congr 1
  simp [hα, MulAut.conj_apply, mul_assoc]

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow.HalfTensor
