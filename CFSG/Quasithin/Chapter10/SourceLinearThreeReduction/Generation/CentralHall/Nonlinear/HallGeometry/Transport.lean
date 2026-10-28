module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Inputs
public import Theory.Representation.OrthogonalFourMinusRankOne.CartanCharacters

/-!
# Lifting the actual diagonal Hall action to Cartan coordinates

Transport the literal quotient-conjugation action through one compatible
product marking. The uniqueness theorem for diagonal-pair actors makes
the pointwise parameters into multiplicative characters. Transport back
gives the original equivariance equation and retains both fixed vectors.
Thus only genuine geometric placement, not a prechosen character map,
remains for the orthogonal row producer.
Source: Aschbacher--Smith, 10.1.2(5) and 10.2.3, pp.742 and 745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02 Representation.OrthogonalFourMinus
open Representation.OrthogonalFourMinus.FiniteModel
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Pointwise geometric realizations suffice to construct the full original
Cartan coordinates, including both multiplicative characters. -/
theorem cartanCoordinates_of_pointwise
    {H : Subgroup G} (B : Subgroup H)
    (hBM : B ≤ D.maximalLocal.subgroupOf H)
    (n : ℕ) [NeZero n]
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (Field n))
    (q : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃*
      (Matrix.SpecialLinearGroup (Fin 2) (Field n) ×
        Matrix.SpecialLinearGroup (Fin 2) (Field n)))
    (hq : ∀ l : L, q (QuotientGroup.mk' (pCore 2 (localOrbit T L))
      ⟨l,le_componentOrbit L T l.property⟩) =
        (e (QuotientGroup.mk' (pCore 2 L) l),1))
    (h : ∀ b : B, ∃ a : (Field n)ˣ × (Field n)ˣ,
      (∀ x, q (action D B hBM b x) =
        (CartanFixed.diagonal n a.1, CartanFixed.diagonal n a.2) * q x *
          (CartanFixed.diagonal n a.1, CartanFixed.diagonal n a.2)⁻¹) ∧
      FiniteModel.action n (CartanFixed.diagonal n a.1)
        (CartanFixed.rootVector n 1) = CartanFixed.rootVector n 1 ∧
      FiniteModel.action n (CartanFixed.diagonal n a.2)
        (CartanFixed.rootVector n 1) = CartanFixed.rootVector n 1) :
    Nonempty (CartanCoordinates D B hBM n e) := by
  let α := (MulAut.congr q).toMonoidHom.comp (action D B hBM)
  have hp : ∀ b, ∃ a : (Field n)ˣ × (Field n)ˣ,
      CartanFixed.diagonalPairAction n a = α b ∧
      FiniteModel.action n (CartanFixed.diagonal n a.1)
        (CartanFixed.rootVector n 1) = CartanFixed.rootVector n 1 ∧
      FiniteModel.action n (CartanFixed.diagonal n a.2)
        (CartanFixed.rootVector n 1) = CartanFixed.rootVector n 1 := by
    intro b
    obtain ⟨a,ha,hf⟩ := h b
    refine ⟨a,?_,hf⟩
    apply MulEquiv.ext
    intro y
    change (CartanFixed.diagonal n a.1, CartanFixed.diagonal n a.2) * y *
        (CartanFixed.diagonal n a.1, CartanFixed.diagonal n a.2)⁻¹ =
      q (action D B hBM b (q.symm y))
    simpa only [q.apply_symm_apply] using (ha (q.symm y)).symm
  obtain ⟨χ,hχ,hfixed⟩ := CartanFixed.exists_characters_of_pointwise_diagonal n α hp
  refine ⟨{ quotientPair := q
            component := hq
            characters := χ
            equivariant := ?_
            fixed := hfixed }⟩
  intro b x
  have he := DFunLike.congr_fun hχ b
  have hx := DFunLike.congr_fun he (q x)
  change (CartanFixed.diagonal n (χ b).1, CartanFixed.diagonal n (χ b).2) * q x *
      (CartanFixed.diagonal n (χ b).1, CartanFixed.diagonal n (χ b).2)⁻¹ =
    q (action D B hBM b (q.symm (q x))) at hx
  rw [q.symm_apply_apply] at hx
  exact hx.symm

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
