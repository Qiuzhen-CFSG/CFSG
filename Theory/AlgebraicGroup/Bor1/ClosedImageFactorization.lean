module

public import Theory.AlgebraicGroup.Morphism.ClosedEmbedding

universe u v

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-!
The final formal step in the Bor1 quotient construction is independent of the
choice of representation.  Once a representation is an isomorphism onto its
closed image, every morphism out of the source can be transported across the
inverse isomorphism.  The kernel hypothesis is only needed earlier, when the
representation with the prescribed kernel is constructed.
-/

public theorem factor_through_closedImage_of_coordinate_embedding
    {G I : Variety k} [AlgebraicGroup G] [AlgebraicGroup I]
    (f : AlgebraicGroup.Morphism G I)
    (hinjective : Function.Injective f.onPoints)
    (hcoordinate : ∀ c : G.Coordinates,
      ∃ q : Variety.PolynomialFunction I,
        Variety.PolynomialFunction.pullback f.toVariety q =
          Variety.PolynomialFunction.ofPolynomial G (MvPolynomial.X c)) :
    let J := f.imageClosedSubgroup
    letI : AlgebraicGroup J.carrierVariety := J.carrierAlgebraicGroup
    ∃ e : AlgebraicGroup.Iso G J.carrierVariety,
      e.hom = f.codRestrictClosedSubgroup J (fun y => ⟨y, rfl⟩) ∧
      ∀ {K : Variety k} (_ : AlgebraicGroup K)
          (φ : AlgebraicGroup.Morphism G K),
          ∃! ψ : AlgebraicGroup.Morphism J.carrierVariety K,
            ψ.comp e.hom = φ := by
  dsimp only
  let J := f.imageClosedSubgroup
  let : AlgebraicGroup J.carrierVariety := J.carrierAlgebraicGroup
  obtain ⟨e, he⟩ := f.iso_imageClosedSubgroup_of_coordinate_preimage
    hinjective hcoordinate
  refine ⟨e, he, ?_⟩
  intro K _ φ
  let ψ : AlgebraicGroup.Morphism J.carrierVariety K := φ.comp e.inv
  refine ⟨ψ, ?_, ?_⟩
  · apply Morphism.ext
    funext x
    change φ.onPoints (e.inv.onPoints (e.hom.onPoints x)) = φ.onPoints x
    rw [e.hom_inv_id]
  · intro ψ' hψ'
    apply Morphism.ext
    funext y
    change ψ'.onPoints y = φ.onPoints (e.inv.onPoints y)
    have h := congrArg (fun m : AlgebraicGroup.Morphism G K =>
      m.onPoints (e.inv.onPoints y)) hψ'
    change ψ'.onPoints (e.hom.onPoints (e.inv.onPoints y)) =
      φ.onPoints (e.inv.onPoints y) at h
    rw [e.inv_hom_id] at h
    exact h

end Theory.AlgebraicGroup.Bor1
