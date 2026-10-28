module

public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction.Model

/-!
# The binary commutant of the SL₃(4) natural-plus-dual module

Commuting an additive map with elementary transvections forces it to be a
field scalar on the natural module. An additive intertwiner from natural to
dual vanishes: its value on each coordinate line must lie in each of the
other two coordinate lines. Inverse transpose gives the reverse statements.
Splitting a binary endomorphism into four blocks therefore computes the full
commutant, without first assuming field linearity.

This supplies the centralizer calculation for the normalizer reduction in
Aschbacher--Smith, proof of 13.8.20, printed p.955 (1 March 2004 manuscript).
-/

public section
noncomputable section
namespace Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction
open Matrix

private lemma natural_transvection {i j : Fin 3} (hij : i ≠ j) (a : F) (v : W) :
    natural (SpecialLinearGroup.transvection hij a) v =
      v + Pi.single i (a * v j) := by
  change ((1 : Matrix (Fin 3) (Fin 3) F) + Matrix.single i j a).mulVec v = _
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  congr 1
  funext k
  by_cases hk : k = i <;> simp [hk]

private lemma dual_transvection {i j : Fin 3} (hij : i ≠ j) (a : F) (v : W) :
    dualCoordinates (SpecialLinearGroup.transvection hij a) v =
      v + Pi.single j (a * v i) := by
  change ((SpecialLinearGroup.transvection hij a)⁻¹).val.transpose.mulVec v = _
  rw [SpecialLinearGroup.transvection_inv, CharTwo.neg_eq,
    SpecialLinearGroup.transvection_coe, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single]
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  congr 1
  funext k
  by_cases hk : k = j <;> simp [hk]

theorem natural_centralizer_scalar (f : W →+ W)
    (hf : ∀ (g : SL) v, f (natural g v) = natural g (f v)) :
    ∃ c : F, ∀ v, f v = c • v := by
  have hsingle {i j : Fin 3} (hij : i ≠ j) (a : F) :
      f (Pi.single i a) = Pi.single i (a * f (Pi.single j 1) j) := by
    have h := hf (SpecialLinearGroup.transvection hij a) (Pi.single j 1)
    rw [natural_transvection, natural_transvection, map_add] at h
    simpa using add_left_cancel h
  have hdiag {i j : Fin 3} (hij : i ≠ j) :
      f (Pi.single i 1) i = f (Pi.single j 1) j := by
    simpa using congrFun (hsingle hij 1) i
  have hs (i : Fin 3) (a : F) :
      f (Pi.single i a) = Pi.single i (a * f (Pi.single 0 1) 0) := by
    obtain ⟨j, hij⟩ : ∃ j : Fin 3, i ≠ j := by fin_cases i <;> decide
    rw [hsingle hij]
    by_cases hj : j = 0
    · rw [hj]
    · rw [hdiag hj]
  refine ⟨f (Pi.single 0 1) 0, fun v => ?_⟩
  have hv : v = ∑ i : Fin 3, Pi.single i (v i) := by
    funext i
    simp [Finset.sum_apply]
  calc
    f v = ∑ i : Fin 3, f (Pi.single i (v i)) := by rw [← map_sum, ← hv]
    _ = ∑ i : Fin 3, Pi.single i (v i * f (Pi.single 0 1) 0) :=
      Finset.sum_congr rfl (fun i _ => hs i (v i))
    _ = f (Pi.single 0 1) 0 • v := by
      funext i
      simp [Finset.sum_apply, mul_comm]

theorem natural_dual_intertwiner_zero (f : W →+ W)
    (hf : ∀ (g : SL) v, f (natural g v) = dualCoordinates g (f v)) : f = 0 := by
  have hsingle {i j : Fin 3} (hij : i ≠ j) (a : F) :
      f (Pi.single i a) = Pi.single j (a * f (Pi.single j 1) i) := by
    have h := hf (SpecialLinearGroup.transvection hij a) (Pi.single j 1)
    rw [natural_transvection, dual_transvection, map_add] at h
    simpa using add_left_cancel h
  have hs (i : Fin 3) (a : F) : f (Pi.single i a) = 0 := by
    funext k
    obtain ⟨j, hij, hkj⟩ : ∃ j : Fin 3, i ≠ j ∧ k ≠ j := by
      fin_cases i <;> fin_cases k <;> decide
    rw [hsingle hij]
    simp [Pi.single_eq_of_ne hkj]
  apply AddMonoidHom.ext
  intro v
  have hv : v = ∑ i : Fin 3, Pi.single i (v i) := by
    funext i
    simp [Finset.sum_apply]
  rw [hv, map_sum]
  simp [hs]

theorem dual_centralizer_scalar (f : W →+ W)
    (hf : ∀ (g : SL) v, f (dualCoordinates g v) = dualCoordinates g (f v)) :
    ∃ c : F, ∀ v, f v = c • v := by
  apply natural_centralizer_scalar f
  intro g v
  have h := hf (SpecialLinearGroup.inverseTranspose g) v
  change f (natural (SpecialLinearGroup.inverseTranspose
    (SpecialLinearGroup.inverseTranspose g)) v) = natural
      (SpecialLinearGroup.inverseTranspose (SpecialLinearGroup.inverseTranspose g)) (f v) at h
  simpa only [inverseTranspose_involutive] using h

theorem dual_natural_intertwiner_zero (f : W →+ W)
    (hf : ∀ (g : SL) v, f (dualCoordinates g v) = natural g (f v)) : f = 0 := by
  apply natural_dual_intertwiner_zero f
  intro g v
  have h := hf (SpecialLinearGroup.inverseTranspose g) v
  change f (natural (SpecialLinearGroup.inverseTranspose
    (SpecialLinearGroup.inverseTranspose g)) v) = dualCoordinates g (f v) at h
  simpa only [inverseTranspose_involutive] using h

theorem centralizer_block_scalars (f : V →ₗ[ZMod 2] V)
    (hf : ∀ (g : SL) v, f (representation g v) = representation g (f v)) :
    ∃ a b : F, ∀ v, f v = (a • v.1, b • v.2) := by
  let inl : W →ₗ[ZMod 2] V := LinearMap.inl (ZMod 2) W W
  let inr : W →ₗ[ZMod 2] V := LinearMap.inr (ZMod 2) W W
  let fst : V →ₗ[ZMod 2] W := LinearMap.fst (ZMod 2) W W
  let snd : V →ₗ[ZMod 2] W := LinearMap.snd (ZMod 2) W W
  let f₁₁ := (fst.comp (f.comp inl)).toAddMonoidHom
  let f₁₂ := (fst.comp (f.comp inr)).toAddMonoidHom
  let f₂₁ := (snd.comp (f.comp inl)).toAddMonoidHom
  let f₂₂ := (snd.comp (f.comp inr)).toAddMonoidHom
  have h₁₁ (g : SL) (v : W) : f₁₁ (natural g v) = natural g (f₁₁ v) := by
    have h := congrArg Prod.fst (hf g (v, 0))
    simpa [f₁₁, fst, inl, representation, Representation.prod] using h
  have h₁₂ (g : SL) (v : W) : f₁₂ (dualCoordinates g v) = natural g (f₁₂ v) := by
    have h := congrArg Prod.fst (hf g (0, v))
    simpa [f₁₂, fst, inr, representation, Representation.prod] using h
  have h₂₁ (g : SL) (v : W) : f₂₁ (natural g v) = dualCoordinates g (f₂₁ v) := by
    have h := congrArg Prod.snd (hf g (v, 0))
    simpa [f₂₁, snd, inl, representation, Representation.prod] using h
  have h₂₂ (g : SL) (v : W) : f₂₂ (dualCoordinates g v) = dualCoordinates g (f₂₂ v) := by
    have h := congrArg Prod.snd (hf g (0, v))
    simpa [f₂₂, snd, inr, representation, Representation.prod] using h
  obtain ⟨a, ha⟩ := natural_centralizer_scalar f₁₁ h₁₁
  obtain ⟨b, hb⟩ := dual_centralizer_scalar f₂₂ h₂₂
  have h₁₂zero := dual_natural_intertwiner_zero f₁₂ h₁₂
  have h₂₁zero := natural_dual_intertwiner_zero f₂₁ h₂₁
  refine ⟨a, b, fun v => ?_⟩
  have hv : v = (v.1, 0) + (0, v.2) := by simp
  have h₁₂v : (f (0, v.2)).1 = 0 := DFunLike.congr_fun h₁₂zero v.2
  have h₂₁v : (f (v.1, 0)).2 = 0 := DFunLike.congr_fun h₂₁zero v.1
  calc
    f v = f (v.1, 0) + f (0, v.2) := by rw [← map_add, ← hv]
    _ = (a • v.1, b • v.2) := by
      apply Prod.ext
      · change (f (v.1, 0)).1 + (f (0, v.2)).1 = a • v.1
        rw [h₁₂v, add_zero]
        exact ha v.1
      · change (f (v.1, 0)).2 + (f (0, v.2)).2 = b • v.2
        rw [h₂₁v, zero_add]
        exact hb v.2

/-- The full binary commutant consists precisely of independent field scalars. -/
theorem commutes_iff_blockScalar (f : V →ₗ[ZMod 2] V) :
    (∀ (g : SL) v, f (representation g v) = representation g (f v)) ↔
      ∃ a b : F, f = blockScalar a b := by
  constructor
  · intro hf
    obtain ⟨a, b, h⟩ := centralizer_block_scalars f hf
    exact ⟨a, b, LinearMap.ext h⟩
  · rintro ⟨a, b, rfl⟩
    exact blockScalar_commutes a b

/-- The only commuting idempotents are zero, identity, and the two summand projections. -/
theorem centralizer_idempotents (f : V →ₗ[ZMod 2] V)
    (hf : ∀ (g : SL) v, f (representation g v) = representation g (f v))
    (hi : f * f = f) :
    f = 0 ∨ f = 1 ∨ f = blockScalar 1 0 ∨ f = blockScalar 0 1 := by
  obtain ⟨a, b, rfl⟩ := (commutes_iff_blockScalar f).mp hf
  have ha : a ^ 2 = a := by
    have h := congrArg (fun z : V => z.1 0)
      (LinearMap.congr_fun hi ((Pi.single 0 1 : W), 0))
    simpa [blockScalar_apply, Module.End.mul_apply, sq] using h
  have hb : b ^ 2 = b := by
    have h := congrArg (fun z : V => z.2 0)
      (LinearMap.congr_fun hi (0, (Pi.single 0 1 : W)))
    simpa [blockScalar_apply, Module.End.mul_apply, sq] using h
  rcases eq_zero_or_one_of_sq_eq_self ha with rfl | rfl <;>
    rcases eq_zero_or_one_of_sq_eq_self hb with rfl | rfl
  · exact Or.inl (by apply LinearMap.ext; intro v; simp [blockScalar_apply])
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inl (by apply LinearMap.ext; intro v; simp [blockScalar_apply]))

end Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction
