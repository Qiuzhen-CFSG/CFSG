module
public import Theory.Representation.OrthogonalFourPlusMatrix.AmbientSemilinear
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Theory.LinearAlgebra.QuadraticRankOneDisplacement
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Basic

/-!
# Small binary displacements in a determinant tensor normalizer

A nonzero displacement of binary rank at most two forces the coefficient
field of a four-dimensional determinant tensor to have degree two. Ambient
semilinearity comes from the actual normal component action. A nontrivial
field twist would move at least half the binary space, so the witness is
field-linear; restriction of scalars then makes the field degree divide its
positive displacement rank.

The original larger-actor consumer uses this bound before applying the
GF(4) normalizer's elementary-subgroup theorem. No exact rank-two or
whole-group identification is assumed.

Source: Aschbacher–Smith, G.11.7, printed p.368 of refs/quasithin.pdf.
-/

public noncomputable section
namespace ClassicalOrthogonal.FourPlusMatrix.LowRankDegree
open Module
variable {F G W : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [Group G] [AddCommGroup W] [Module (ZMod 2) W]

/-- A nonzero displacement of binary rank at most two in the actual tensor
normalizer forces coefficient degree two. -/
theorem field_degree_eq_two_of_small_equivariant
    (ρ : Representation (ZMod 2) G W) (N : Subgroup G) [N.Normal]
    (e : N ≃* PairSL (F := F)) (f : W ≃ₗ[ZMod 2] Mat (F := F))
    (hf : ∀ (n : N) (w : W), f (ρ n w) = representation (e n) (f w))
    (hn : 2 ≤ finrank (ZMod 2) F) (a : G)
    (hpos : 0 < finrank (ZMod 2) (Representation.RankTwo.movedSpace ρ a))
    (hr : finrank (ZMod 2) (Representation.RankTwo.movedSpace ρ a) ≤ 2) :
    finrank (ZMod 2) F = 2 := by
  let τ : Representation (ZMod 2) G (Mat (F := F)) := f.conjRingEquiv.toMonoidHom.comp ρ
  have hcoord (n : N) (M : Mat (F := F)) : τ n M = matrixAction (e n) M := by
    change f (ρ n (f.symm M)) = _
    rw [hf,f.apply_symm_apply]
    rfl
  obtain ⟨φ,hφ⟩ := normal_ambient_semilinear N e τ hcoord
  let t := LinearMap.GeneralLinearGroup.toLinearEquiv (τ.asGroupHom a)
  have he (g : G) (w : W) : f (ρ g w) = τ g (f w) := by
    change f (ρ g w) = f (ρ g (f.symm (f w)))
    rw [f.symm_apply_apply]
  have hrank := Representation.RankTwo.finrank_movedSpace_transport ρ τ
    (MulEquiv.refl G) f he a
  have hp : 0 < finrank (ZMod 2) (LinearMap.range (t.toLinearMap-LinearMap.id)) := by
    change 0 < finrank (ZMod 2) (Representation.RankTwo.movedSpace τ a)
    exact lt_of_lt_of_eq hpos hrank
  have hu : finrank (ZMod 2) (LinearMap.range (t.toLinearMap-LinearMap.id)) ≤ 2 := by
    change finrank (ZMod 2) (Representation.RankTwo.movedSpace τ a) ≤ 2
    exact hrank.symm.trans_le hr
  have hdim : finrank (ZMod 2) (Mat (F := F)) = finrank (ZMod 2) F * 4 := by
    rw [←Module.finrank_mul_finrank (ZMod 2) F]
    congr 1
    change finrank F (Matrix (Fin 2) (Fin 2) F) = 4
    rw [finrank_matrix]
    norm_num
  have hlin (c : F) (M : Mat (F := F)) : t (c • M) = c • t M := by
    have hs (c : F) : φ a c = c := by
      by_contra hc
      have hb := Representation.BinaryOffender.NaturalTensor.finrank_le_twice_operatorFixedCodim
        t.toLinearMap (φ a).toRingHom ⟨c,hc⟩ (hφ a)
      change finrank (ZMod 2) (Mat (F := F)) ≤
        2 * finrank (ZMod 2) (LinearMap.range (t.toLinearMap-LinearMap.id)) at hb
      rw [hdim] at hb
      omega
    exact (hφ a c M).trans (congrArg (fun d : F => d • t M) (hs c))
  let tF : Mat (F := F) →ₗ[F] Mat (F := F) :=
    { toFun := t, map_add' := t.map_add, map_smul' := hlin }
  let eF := LinearEquiv.ofBijective tF t.bijective
  have heF : eF.restrictScalars (ZMod 2) = t := by ext M; rfl
  have hd := QuadraticForm.displacement_rank_restrictScalars (k := ZMod 2) eF
  rw [heF] at hd
  have hpositive : 0 < finrank F (LinearMap.range (eF.toLinearMap-LinearMap.id)) := by
    by_contra hh
    have hz : finrank F (LinearMap.range (eF.toLinearMap-LinearMap.id)) = 0 := by omega
    rw [hz,mul_zero] at hd
    omega
  nlinarith
end ClassicalOrthogonal.FourPlusMatrix.LowRankDegree
