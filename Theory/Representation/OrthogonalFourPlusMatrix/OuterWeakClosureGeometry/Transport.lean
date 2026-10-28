module

public import Theory.Representation.OrthogonalFourPlusMatrix.NearOffenderSwap
public import Theory.Representation.OrthogonalFourPlusMatrix.Comparison.RankOne

/-!
# Inner coordinates for outer fixed-line actors

A nonzero singular matrix lies in the inner orbit of the upper matrix unit.
Fixing its whole coefficient line makes a binary normalizer actor linear
over the field. Conjugating by the same inner coordinate gives an actual
field-linear determinant-isometry action fixing the standard matrix unit.
Faithfulness, elementary commutation, order, and the presence of an outer
operator are retained, as is the literal intertwining identity.

This supplies the coordinate bridge into the outer branch of
Aschbacher–Smith 9.4.5, combined manuscript, printed pp.736–737.
-/

@[expose] public noncomputable section
open Module Matrix Subgroup
open Representation.BinaryOffender Representation.BinaryOffender.NaturalTensor
namespace ClassicalOrthogonal.FourPlusMatrix.Binary

local instance : Finite (Module.End (ZMod 2) V) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

/-- Inner coordinates carry the standard singular unit to any nonzero singular matrix. -/
theorem exists_inner_singular_coordinates (v : V) (hv : v ≠ 0) (hs : v.det = 0) :
    ∃ g : G, matrixHom g (Matrix.single 0 1 1) = v := by
  obtain ⟨A,B,hv⟩ := ComparisonAux.MatrixTwo.singular_nonzero_SL2_orbit v hv hs
  let J : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![0,1;1,0],by simp [Matrix.det_fin_two,CharTwo.neg_eq]⟩
  have hJ : J * J = 1 := by
    apply Subtype.ext
    change J.val * J.val = (1 : V)
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [J,Matrix.mul_apply,Fin.sum_univ_two]
  have hJi : J⁻¹ = J := inv_eq_of_mul_eq_one_left hJ
  have he : matrixHom (1,J) (Matrix.single 0 1 1) =
      ComparisonAux.MatrixTwo.E11 := by
    change (1 : V) * Matrix.single 0 1 1 * J⁻¹.val = _
    rw [hJi,one_mul]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [J,Matrix.mul_apply,ComparisonAux.MatrixTwo.E11,Matrix.single]
  refine ⟨(A,B)*(1,J),?_⟩
  rw [map_mul]
  change matrixHom (A,B) (matrixHom (1,J) (Matrix.single 0 1 1)) = v
  rw [he]
  exact hv.symm

/-- The normalized field action, with all hypotheses and its original actor retained. -/
structure OuterFixedLineActor (B : Subgroup (linearNormalizer action)) where
  coordinate : G
  fieldAction : B →* (V ≃ₗ[F] V)
  injective : Function.Injective fieldAction
  determinant : ∀ h M, (fieldAction h M).det = M.det
  commuting : ∀ a b, fieldAction a * fieldAction b = fieldAction b * fieldAction a
  involutions : ∀ h M, fieldAction h (fieldAction h M) = M
  fixesUnit : ∀ h, fieldAction h (Matrix.single 0 1 1) = Matrix.single 0 1 1
  card_ge_eight : 8 ≤ Nat.card B
  outer : ∃ t : B, ∀ g : G, fieldAction t ≠ matrixHom g
  equivariant : ∀ h M,
    matrixHom coordinate (fieldAction h M) = h.val.val.val (matrixHom coordinate M)

/-- An outer elementary actor fixing a coefficient line supplies the normalized action. -/
theorem exists_outerFixedLineActor
    (B : Subgroup (linearNormalizer action)) (hB : IsElementaryTwo B)
    (hr : 3 ≤ rank B)
    (houter : ¬ B.map (linearNormalizer action).subtype ≤ actionImage action)
    (v : V) (hv : v ≠ 0) (hs : v.det = 0)
    (hfix : ∀ h : B, ∀ c : F, h.val.val.val (c • v) = c • v) :
    Nonempty (OuterFixedLineActor B) := by
  let := hB.2
  have hi (h : B) : h*h = 1 := by
    apply Subtype.ext
    change h.val * h.val = 1
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
      h.val h.property
  obtain ⟨f,hfi,hf⟩ := exists_field_actor_hom B (by
    intro t ht
    exact normalizer_field_linear_of_fixed_scalar_orbit
      (LinearMap.GeneralLinearGroup.toLinearEquiv t.val) (normalizer_linearEquiv_mem t)
      v hv (hfix ⟨t,ht⟩))
  have hft (h : B) : (f h).restrictScalars (ZMod 2) =
      LinearMap.GeneralLinearGroup.toLinearEquiv h.val.val := by
    apply LinearEquiv.ext
    intro w
    exact hf h w
  have hdet (h : B) (M : V) : (f h M).det = M.det := by
    apply field_involution_preserves_det (f h)
    · rw [hft]
      exact normalizer_linearEquiv_mem h.val
    · intro w
      have hh : f h * f h = 1 := by rw [←map_mul,hi,map_one]
      exact LinearEquiv.congr_fun hh w
  obtain ⟨g,hg⟩ := exists_inner_singular_coordinates v hv hs
  let q : B →* (V ≃ₗ[F] V) := (MulAut.conj (matrixHom g)⁻¹).toMonoidHom.comp f
  have hq (h : B) (M : V) : q h M = (matrixHom g)⁻¹ (f h (matrixHom g M)) := rfl
  refine ⟨{
    coordinate := g
    fieldAction := q
    injective := (MulAut.conj (matrixHom g)⁻¹).injective.comp hfi
    determinant := ?_
    commuting := ?_
    involutions := ?_
    fixesUnit := ?_
    card_ge_eight := ?_
    outer := ?_
    equivariant := ?_ }⟩
  · intro h M
    rw [hq,←map_inv]
    exact (matrixAction_det g⁻¹ _).trans ((hdet h _).trans (matrixAction_det g M))
  · intro a b
    rw [←map_mul,←map_mul,mul_comm' a b]
  · intro h M
    have hh : q h * q h = 1 := by rw [←map_mul,hi,map_one]
    exact LinearEquiv.congr_fun hh M
  · intro h
    rw [hq,hg,hf]
    have hh : h.val.val.val v = v := by simpa only [one_smul] using hfix h 1
    rw [hh,←hg]
    exact (matrixHom g).symm_apply_apply _
  · rw [hB.card_eq_two_pow_rank]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hr
  · obtain ⟨u,hu,hou⟩ := SetLike.not_le_iff_exists.mp houter
    obtain ⟨t,ht,rfl⟩ := hu
    let a : B := ⟨t,ht⟩
    refine ⟨a,?_⟩
    intro r he
    apply hou
    have he' := congrArg (MulAut.conj (matrixHom g)) he
    have heq : f a = matrixHom (g*r*g⁻¹) := by
      simpa [q,MulAut.conj_apply,map_mul,map_inv,mul_assoc] using he'
    refine ⟨g*r*g⁻¹,?_⟩
    apply Units.ext
    apply LinearMap.ext
    intro w
    change action (g*r*g⁻¹) w = a.val.val.val w
    rw [←hf,heq]
    rfl
  · intro h M
    rw [hq]
    change (matrixHom g) ((matrixHom g).symm (f h (matrixHom g M))) = _
    rw [LinearEquiv.apply_symm_apply,hf]

end ClassicalOrthogonal.FourPlusMatrix.Binary
