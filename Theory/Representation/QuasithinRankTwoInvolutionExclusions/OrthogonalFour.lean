module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OrthogonalFour.RankOne
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OrthogonalFour.Swap
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OrthogonalFour.TensorModel
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Basic
public import Theory.Representation.OrthogonalFourPlusMatrix.LowRank
public import Theory.Representation.OrthogonalFourPlusMatrix.InvariantQuadratic
public import Theory.Representation.OrthogonalFourPlusMatrix.Comparison

/-!
# Rank-two involutions in the Ω₄⁺(4) extension case

The full binary normalizer of the actual SL₂(4) × SL₂(4) determinant action
is semilinear over F₄. A nontrivial field twist moves at least four binary
dimensions. A rank-two involution is therefore F₄-linear, has field rank one,
and preserves the determinant. The rank-one classification identifies it
with a conjugate of adjugation, the factor swap. An explicit SL₂ element
then gives a conjugate product of order five.

The final adapters retain the literal normal subgroup, conjugation
`v^h = h⁻¹ v h`, and equivariant identifications with either the tensor
of the two natural modules or the existing PΩ₄⁺(4) natural module. They
exclude a rank-two member of elementary abelian X under the product-order
bound supplied by the parent symplectic argument. The calculation covers
the full normalizer, including field actors and field-swap products; it
requires no additional G.10.1/G.11.1 action premise. In fact X not being
contained in F*(H) is unnecessary for this stronger concrete exclusion.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, G.11.2(7), printed p.364 (PDF p.375),
and the proof of 6.2.19, printed p.691 (PDF p.708).
-/

@[expose] public noncomputable section
namespace Representation.RankTwo.OrthogonalFour
open ClassicalOrthogonal.FourPlusMatrix
open ClassicalOrthogonal.FourPlusMatrix.Binary
open Matrix Module

/-- There is exactly one possible rank-two involution class in the full binary
normalizer: the conjugates of the factor swap by the special linear factors. -/
theorem rank_two_class (t : V ≃ₗ[ZMod 2] V)
    (hn : t ∈ Subgroup.normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)))
    (h2 : t ^ 2 = 1)
    (hr : finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2) :
    ∃ a : G, t = linearAction a * binarySwap * (linearAction a)⁻¹ := by
  have hne : t ≠ 1 := by
    intro he
    have hz : t.toLinearMap - LinearMap.id = 0 := by
      rw [he]
      exact sub_self _
    rw [hz, LinearMap.range_zero, finrank_bot] at hr
    omega
  obtain ⟨s, hs, hsr, _⟩ := low_rank_nonidentity t hn hr.le hne
  have hs2 (M : V) : s (s M) = M := by
    have he : t (t M) = M := LinearEquiv.congr_fun (show t * t = 1 by
      simpa only [pow_two] using h2) M
    rw [← hs] at he
    exact he
  have hsne : s ≠ 1 := by
    intro he
    apply hne
    rw [← hs, he]
    rfl
  obtain ⟨A, hA⟩ := rank_one_sandwich s hsne hsr.le
    (field_involution_preserves_det s (hs.symm ▸ hn) hs2)
  refine ⟨(A, 1), ?_⟩
  apply LinearEquiv.ext
  intro M
  have htM : t M = A.val * M.adjugate * A.val := by
    rw [← hs]
    exact hA M
  rw [htM, conjugate_swap_apply]

/-- A rank-two normalizer involution has an inner conjugate whose product with
it has order five. In particular field twists and their products with swaps
introduce no omitted rank-two class. -/
theorem rank_two_product_order_five (t : V ≃ₗ[ZMod 2] V)
    (hn : t ∈ Subgroup.normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)))
    (h2 : t ^ 2 = 1)
    (hr : finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2) :
    ∃ g : G, orderOf (t * ((linearAction g)⁻¹ * t * linearAction g)) = 5 := by
  obtain ⟨a, rfl⟩ := rank_two_class t hn h2 hr
  exact conjugate_swap_product a

/-- Concrete exclusion with the literal normal-subgroup action image. Only the
involution and rank hypotheses on the chosen member of X are needed. -/
theorem exclusion_of_image {H : Type*} [Group H] [Finite H]
    (ρ : H →* (V ≃ₗ[ZMod 2] V)) (N : Subgroup H) [N.Normal]
    (himage : N.map ρ = linearAction.range) (v : H) (h2 : v ^ 2 = 1)
    (hr : finrank (ZMod 2) (LinearMap.range ((ρ v).toLinearMap - LinearMap.id)) = 2)
    (hbound : ∀ h : H, orderOf (v * (h⁻¹ * v * h)) ≤ 4) : False := by
  have hn : ρ v ∈ Subgroup.normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)) := by
    rw [← himage]
    apply Subgroup.le_normalizer_map ρ
    apply Subgroup.mem_map_of_mem
    rw [Subgroup.normalizer_eq_top]
    trivial
  obtain ⟨g, hg⟩ := rank_two_product_order_five (ρ v) hn
    (by rw [← map_pow, h2, map_one]) hr
  obtain ⟨n, hnN, hn⟩ : ∃ n ∈ N, ρ n = linearAction g := by
    apply (Subgroup.mem_map).mp
    rw [himage]
    exact ⟨g, rfl⟩
  have hd : 5 ∣ orderOf (v * (n⁻¹ * v * n)) := by
    have hd := orderOf_map_dvd ρ (v * (n⁻¹ * v * n))
    simpa only [map_mul, map_inv, hn, hg] using hd
  have hlo := Nat.le_of_dvd (orderOf_pos (v * (n⁻¹ * v * n))) hd
  have hhi := hbound n
  omega

section Transport
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]

private def coordinateAction (ρ : Representation (ZMod 2) H W)
    (f : W ≃ₗ[ZMod 2] V) : H →* (V ≃ₗ[ZMod 2] V) where
  toFun g := f.symm.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W (ρ.asGroupHom g)).trans f)
  map_one' := by
    apply LinearEquiv.ext
    intro M
    change f (ρ 1 (f.symm M)) = M
    simp
  map_mul' g h := by
    apply LinearEquiv.ext
    intro M
    change f (ρ (g * h) (f.symm M)) =
      f (ρ g (f.symm (f (ρ h (f.symm M)))))
    rw [f.symm_apply_apply, map_mul, Module.End.mul_apply]

/-- Equivariant transport from the actual two-factor action, retaining the
normal subgroup and the original conjugation convention. -/
theorem exclusion_of_equivariant_matrix_model [Finite H]
    (ρ : Representation (ZMod 2) H W) (N : Subgroup H) [N.Normal]
    (e : N ≃* G) (f : W ≃ₗ[ZMod 2] V)
    (hf : ∀ (n : N) (w : W), f (ρ n w) = action (e n) (f w))
    (v : H) (h2 : v ^ 2 = 1)
    (hr : finrank (ZMod 2) (movedSpace ρ v) = 2)
    (hbound : ∀ h : H, orderOf (v * (h⁻¹ * v * h)) ≤ 4) : False := by
  let τ := coordinateAction ρ f
  have ht (n : N) : τ n = linearAction (e n) := by
    apply LinearEquiv.ext
    intro M
    change f (ρ n (f.symm M)) = action (e n) M
    rw [hf, f.apply_symm_apply]
  have himage : N.map τ = linearAction.range := by
    ext t
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨e ⟨n, hn⟩, (ht ⟨n, hn⟩).symm⟩
    · rintro ⟨g, rfl⟩
      refine ⟨e.symm g, (e.symm g).property, ?_⟩
      rw [ht, e.apply_symm_apply]
  let σ : Representation (ZMod 2) H V :=
    { toFun g := (τ g).toLinearMap
      map_one' := congrArg LinearEquiv.toLinearMap τ.map_one
      map_mul' g h := congrArg LinearEquiv.toLinearMap (τ.map_mul g h) }
  have hs (g : H) (w : W) : f (ρ g w) = σ g (f w) := by
    change f (ρ g w) = f (ρ g (f.symm (f w)))
    rw [f.symm_apply_apply]
  have hd := finrank_movedSpace_transport ρ σ (MulEquiv.refl H) f hs v
  apply exclusion_of_image τ N himage v h2 _ hbound
  change finrank (ZMod 2) (movedSpace σ v) = 2
  exact hd.symm.trans hr

/-- An actual tensor of the two natural SL₂(4) modules supplies the required
matrix identification, including the binary restriction of scalars. -/
theorem exclusion_of_tensor_model [Finite H]
    (ρ : Representation (ZMod 2) H W) (N : Subgroup H) [N.Normal]
    (e : N ≃* G)
    (f : W ≃ₗ[ZMod 2] TensorProduct F (Fin 2 → F) (Fin 2 → F))
    (hf : ∀ (n : N) (w : W), f (ρ n w) = tensorRepresentation (e n) (f w))
    (v : H) (h2 : v ^ 2 = 1)
    (hr : finrank (ZMod 2) (movedSpace ρ v) = 2)
    (hbound : ∀ h : H, orderOf (v * (h⁻¹ * v * h)) ≤ 4) : False := by
  apply exclusion_of_equivariant_matrix_model ρ N e
    (f.trans (tensorCoordinates.restrictScalars (ZMod 2))) _ v h2 hr hbound
  intro n w
  change tensorCoordinates (f (ρ n w)) = action (e n) (tensorCoordinates (f w))
  rw [hf]
  exact tensorCoordinates_equivariant (e n) (f w)

/-- Source-facing version using the existing PΩ₄⁺(4) carrier and its actual
natural orthogonal representation. No extension class or rank conclusion is
assumed in the model identification. -/
theorem exclusion_of_orthogonal_model [Finite H]
    (ρ : Representation (ZMod 2) H W) (N : Subgroup H) [N.Normal]
    (e : N ≃* ClassicalOrthogonal.POmegaPlus 2 F)
    (f : W ≃ₗ[ZMod 2] ClassicalOrthogonal.VectorD 2 F)
    (hf : ∀ (n : N) (w : W), f (ρ n w) =
      ClassicalOrthogonal.projectiveElementaryNatural (ClassicalOrthogonal.formD 2 F)
        (e n) (f w))
    (v : H) (h2 : v ^ 2 = 1)
    (hr : finrank (ZMod 2) (movedSpace ρ v) = 2)
    (hbound : ∀ h : H, orderOf (v * (h⁻¹ * v * h)) ≤ 4) : False := by
  apply exclusion_of_equivariant_matrix_model ρ N (e.trans orthogonalEquiv.symm)
    (f.trans binaryCoordinates) _ v h2 hr hbound
  intro n w
  change binaryCoordinates (f (ρ n w)) =
    action (orthogonalEquiv.symm (e n)) (binaryCoordinates (f w))
  rw [hf]
  have he := binaryCoordinates_projective_equivariant (orthogonalEquiv.symm (e n)) (f w)
  rw [orthogonalEquiv.apply_symm_apply] at he
  exact he

/-- The G.11.2(7) exclusion for a specified member of the elementary abelian X.
No additional X-action hypothesis is required by the concrete calculation. -/
theorem exclusion_of_elementary_orthogonal_model [Finite H]
    (ρ : Representation (ZMod 2) H W) (N : Subgroup H) [N.Normal]
    (e : N ≃* ClassicalOrthogonal.POmegaPlus 2 F)
    (f : W ≃ₗ[ZMod 2] ClassicalOrthogonal.VectorD 2 F)
    (hf : ∀ (n : N) (w : W), f (ρ n w) =
      ClassicalOrthogonal.projectiveElementaryNatural (ClassicalOrthogonal.formD 2 F)
        (e n) (f w))
    (X : Subgroup H) [IsElementaryAbelian 2 X] (v : H) (hv : v ∈ X)
    (hr : finrank (ZMod 2) (movedSpace ρ v) = 2)
    (hbound : ∀ h : H, orderOf (v * (h⁻¹ * v * h)) ≤ 4) : False :=
  exclusion_of_orthogonal_model ρ N e f hf v
    (elemPow_eq_one_of_isElementaryAbelian v hv) hr hbound

end Transport

end Representation.RankTwo.OrthogonalFour
