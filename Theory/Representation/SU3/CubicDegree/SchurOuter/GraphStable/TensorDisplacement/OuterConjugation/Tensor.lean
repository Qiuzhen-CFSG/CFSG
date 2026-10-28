module

public import Theory.Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement.Operators

/-!
# Tensoring the outer adjoint intertwiners

An adjoint-only word admits a transpose-conjugate operator implementing any
relation on group representatives implemented on each adjoint factor. The
induction tensors both the operators and their actual linear coordinates,
keeps trivial factors, and advances the coefficient embedding by Frobenius at
every position. It requires neither a single adjoint factor nor a degree bound.

The factor premise is consumed for the literal SU₃ quotient action in
`GraphStable.Displacement.Conjugation`. Its separate geometric producer must
supply the adjoint intertwiners for all the embeddings encountered here.
Source: Guralnick--Malle, Classification of 2F-modules II, Proposition 4.11,
internal pp.31--32, with §2.2 and §3.5.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct MatrixGroups
open Representation.SL3.BinaryDefiningFactors
namespace Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement.OuterConjugation
variable {F K G : Type*} [Field F] [Field K] [CharP K 2] [Group G]

omit [CharP K 2] in
private theorem tensor_coordinates
    {U W : Type*} [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
    (S c : U ≃ₗ[K] U) (T d : W ≃ₗ[K] W)
    (B : Module.End K U) (C : Module.End K W)
    (hS : ∀ x, c (S x) = B (c x)) (hT : ∀ y, d (T y) = C (d y)) :
    ∀ z, TensorProduct.congr c d (TensorProduct.congr S T z) =
      TensorProduct.map B C (TensorProduct.congr c d z) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => simp only [TensorProduct.congr_tmul, TensorProduct.map_tmul, hS, hT]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Tensor all adjoint intertwiners, retaining their successive Frobenius embeddings. -/
theorem word_intertwiner_of_adjoint_intertwiners
    (π : G →* SL(3,F)) (R : G → G → Prop)
    (hf : ∀ ι : F →+* K,
      ∃ S c : Space K .adjoint ≃ₗ[K] Space K .adjoint,
        (∀ x, c (S x) = adjointTranspose (c x)) ∧
        ∀ g h, R g h →
          S.toLinearMap * factorRep ι .adjoint (π g) =
            factorRep ι .adjoint (π h) * S.toLinearMap)
    (ι : F →+* K) (w : List Factor) (hn : naturalCount w = 0) :
    ∃ S c : WordSpace K w ≃ₗ[K] WordSpace K w,
      (∀ x, c (S x) = wordTranspose w (c x)) ∧
      ∀ g h, R g h →
        S.toLinearMap * wordRep ι w (π g) = wordRep ι w (π h) * S.toLinearMap := by
  induction w generalizing ι with
  | nil =>
    refine ⟨LinearEquiv.refl K _, LinearEquiv.refl K _, fun _ => rfl, ?_⟩
    intro g h _
    rfl
  | cons a w ih =>
    have hn' : naturalCount w = 0 := by
      cases a <;> simp_all [naturalCount]
    obtain ⟨T, d, hd, hT⟩ := ih ((frobenius K 2).comp ι) hn'
    have hf' : ∃ S c : Space K a ≃ₗ[K] Space K a,
        (∀ x, c (S x) = factorTranspose a (c x)) ∧
        ∀ g h, R g h → S.toLinearMap * factorRep ι a (π g) =
          factorRep ι a (π h) * S.toLinearMap := by
      cases a with
      | trivial =>
        exact ⟨LinearEquiv.refl K _, LinearEquiv.refl K _, fun _ => rfl,
          fun _ _ _ => rfl⟩
      | adjoint => exact hf ι
      | natural => simp [naturalCount] at hn
      | dual => simp [naturalCount] at hn
    obtain ⟨S, c, hc, hS⟩ := hf'
    refine ⟨TensorProduct.congr S T, TensorProduct.congr c d, ?_, ?_⟩
    · exact tensor_coordinates S c T d (factorTranspose a) (wordTranspose w) hc hd
    · intro g h hR
      change TensorProduct.map S.toLinearMap T.toLinearMap *
        TensorProduct.map (factorRep ι a (π g)) _ =
        TensorProduct.map (factorRep ι a (π h)) _ *
          TensorProduct.map S.toLinearMap T.toLinearMap
      rw [← TensorProduct.map_mul, ← TensorProduct.map_mul, hS g h hR, hT g h hR]

end Representation.SU3.CubicDegree.SchurOuter.GraphStable.TensorDisplacement.OuterConjugation
