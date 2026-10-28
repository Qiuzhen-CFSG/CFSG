module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.HalfTensor.Model
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.HalfTensor.SchurDescent
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.HalfTensor.Swap
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.HalfTensor.Recognition
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.HalfTensor.PairDisplacement
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow

/-!
# Displacement in the half-field natural G₂ tensor

For a faithful irreducible binary representation of degree `18*r`, the actual
tensor classification identifies its Schur-field extension with two natural
factors at Frobenius positions `i` and `i+s`, where `r = 2*s`. Absolute
irreducibility over the Schur field transfers through this exact intertwiner.
The concrete pair calculation gives displacement at least sixteen for inner
involutions and fifteen for involutory factor exchanges.

The proof constructs the original Schur-linear actor over its Schur field,
extends scalars, retains its induced group automorphism, and descends the rank
bound to binary dimensions. The theorem `bound` proves the literal `hhalf`
premise of `TensorWindow.window_of_coarse_and_half_tensor_estimates`, with no
automorphism-rank, offender, or cubic hypothesis. The consumer
`window_of_coarse_estimate` discharges that premise; the coarse estimate and
automorphism-rank input remain with the tensor-window assembly owner.

Source: Guralnick–Malle, Classification of 2F-modules II, §3.5 and Lemma 8.5,
manuscript pp.20,55–56; see `G2CubicDegree/Source.md`.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped MonoidAlgebra TensorProduct
open Representation Representation.BinaryOffender
open Representation.BinaryOffender.SchurNormalizer
open Representation.BinaryOffender.NaturalTensor

namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow.HalfTensor
section PairEquiv
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (σ : Representation (ZMod 2) (Atlas.G2.Model F) V) [IsIrreducible σ]
  (K : Type*) [Field K] [Algebra (Module.End (ZMod 2)[Atlas.G2.Model F] σ.asModule) K]
  [Algebra F K]

/-- The actual pair realization and its operator estimate discharge the binary `hhalf` bound. -/
theorem bound_of_pair_equiv {r : ℕ} (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r)
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) V = 18 * r)
    (i : ℕ) (e : (extendScalars K σ.endFieldRep).Equiv
      (pairRep F K i (schurDegree 2 σ)))
    (hpair : ∀ (T : Module.End K (PairSpace F K)) (α : MulAut (Atlas.G2.Model F)),
      T ≠ 1 → T * T = 1 →
      (∀ g, T * pairRep F K i (schurDegree 2 σ) g =
        pairRep F K i (schurDegree 2 σ) (α g) * T) →
      15 ≤ operatorFixedCodim (k := K) (V := PairSpace F K) T)
    (t : linearNormalizer σ) (ht : t ≠ 1) (ht2 : t ^ 2 = 1)
    (hs : IsSchurLinear σ t) :
    5 * Module.finrank (ZMod 2) V ≤
      12 * fixedCodim (normalizerRepresentation σ) (Subgroup.zpowers t) := by
  apply displacement_bound_of_split_rank σ hr hF hf hd K t hs
  exact split_rank_of_equiv (W := PairSpace F K) σ K hf
    (pairRep F K i (schurDegree 2 σ)) e hpair t ht ht2 hs

end PairEquiv

variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (σ : Representation (ZMod 2) (Atlas.G2.Model F) V) [IsIrreducible σ]

attribute [local instance] ZMod.algebra

/-- Every nonidentity Schur-linear normalizing involution in binary degree
`18*r` moves at least `5/12` of the module. The genuine natural-pair recognition,
its irreducibility, and both inner and outer displacement cases are discharged. -/
theorem bound {r : ℕ} (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r)
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) V = 18 * r)
    (t : linearNormalizer σ) (ht : t ≠ 1) (ht2 : t ^ 2 = 1)
    (hs : IsSchurLinear σ t) :
    5 * Module.finrank (ZMod 2) V ≤
      12 * fixedCodim (normalizerRepresentation σ) (Subgroup.zpowers t) := by
  let E := Module.End (ZMod 2)[Atlas.G2.Model F] σ.asModule
  let K := AlgebraicClosure E
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  let : CharP K 2 := charP_of_injective_algebraMap (algebraMap E K).injective 2
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let ι : F →+* K := (IsAlgClosed.lift (R := ZMod 2) (S := F) (M := K)).toRingHom
  let : Algebra F K := ι.toAlgebra
  let : IsAbsolutelyIrreducible σ.endFieldRep := endFieldRep_isAbsolutelyIrreducible σ
  let : IsIrreducible (extendScalars K σ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension σ.endFieldRep K
  obtain ⟨i, _, ⟨e⟩⟩ := exists_pairRep_equiv K σ hr hF hf hd
  let : IsIrreducible (k := K) (G := Atlas.G2.Model F) (V := PairSpace F K)
      (pairRep F K i (schurDegree 2 σ)) :=
    (RepEquiv.irreducible_euqiv (RepEquiv.ofRepresentationEquiv e)).mp inferInstance
  have hF' : Nat.card F = 2 ^ (2 * schurDegree 2 σ) :=
    (twice_schurDegree σ hr hF hf hd) ▸ hF
  exact bound_of_pair_equiv σ K hr hF hf hd i e
    (pair_displacement F K i (schurDegree 2 σ) (schurDegree_pos 2 σ) hF')
    t ht ht2 hs

open Subgroup Theory.GroupTheory

/-- Apply the proved half-field estimate to the literal cubic tensor-window
consumer. Only its independent coarse and automorphism-rank estimates remain. -/
theorem window_of_coarse_estimate {r : ℕ} (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r)
    (hf : Function.Injective σ)
    (hAut : primeRank 2 (MulAut (Atlas.G2.Model F)) ≤ 3 * r)
    (hcoarse : ∀ A : Subgroup (linearNormalizer σ), IsElementaryTwo A →
      fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A →
        Module.finrank (ZMod 2) V < 34 * r) :
    ∀ A : Subgroup (linearNormalizer σ),
      IsElementaryTwo A → IsCubic (normalizerRepresentation σ) A →
      fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A →
      Module.finrank (ZMod 2) V < 18 * r := by
  exact window_of_coarse_and_half_tensor_estimates σ hr hF hf hAut hcoarse
    (bound σ hr hF hf)

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow.HalfTensor
