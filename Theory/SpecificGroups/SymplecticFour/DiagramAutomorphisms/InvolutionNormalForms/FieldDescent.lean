module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.OuterReduction
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.FieldDescent.FixedSpace
public import Theory.SpecificGroups.PSp4Three.MatrixModel

/-!
# Symplectic field-involution cocycle descent

Given g σ(g) = 1, the map v ↦ g σ(v) is a semilinear involution. Its fixed
space has dimension four over the fixed field, and its restricted alternating
form is nondegenerate. An isometry to the standard form over that subfield
supplies four fixed columns whose Gram matrix is the standard symplectic
matrix. The resulting matrix h is genuinely symplectic and satisfies
g σ(h) = h, hence g = h σ(h)⁻¹.

The general construction applies to every nontrivial involution of a finite
coefficient field. The exact Frobenius-order theorem specializes it to the
half-Frobenius involution over fields of order 2^n with positive even n.
`Basic.inner_twist_isConj` then gives actual inner conjugacy of automorphisms.
No semilinear automorphism-classification or Lang theorem is assumed.

Source: the symplectic field case of Aschbacher–Smith, Lemma 16.1.4(4),
printed p.1171, with the conventions of Notation 16.1.3 on pp.1170–1171
of `refs/quasithin.pdf`. Fixed-group and residual calculations are separate.
-/

public section
noncomputable section

open Matrix
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
open FieldDescent
variable {F : Type*} [Field F]

private def twist (σ : F ≃+* F) (g : Sp F) : Vector F →+ Vector F where
  toFun v := g.val *ᵥ (σ ∘ v)
  map_zero' := by simp
  map_add' v w := by
    change g.val *ᵥ (σ ∘ (v + w)) = _
    have he : σ ∘ (v + w) = (σ ∘ v) + (σ ∘ w) := by ext i; simp
    rw [he, Matrix.mulVec_add]

private theorem twist_smul (σ : F ≃+* F) (g : Sp F) (a : F) (v : Vector F) :
    twist σ g (a • v) = σ a • twist σ g v := by
  change g.val *ᵥ (σ ∘ (a • v)) = _
  have he : σ ∘ (a • v) = σ a • (σ ∘ v) := by ext i; simp
  rw [he, Matrix.mulVec_smul]
  rfl

private theorem twist_square (σ : F ≃+* F) (hσ : σ ^ 2 = 1)
    (g : Sp F) (hg : g * fieldAutomorphism σ g = 1) (v : Vector F) :
    twist σ g (twist σ g v) = v := by
  have hσσ (a : F) : σ (σ a) = a := congrArg (fun e : F ≃+* F => e a) hσ
  have hc : g.val * g.val.map σ = 1 := congrArg Subtype.val hg
  have he : σ ∘ (g.val *ᵥ (σ ∘ v)) = g.val.map σ *ᵥ v := by
    ext i
    change σ.toRingHom ((g.val *ᵥ (σ ∘ v)) i) = _
    rw [σ.toRingHom.map_mulVec]
    congr 2
    exact funext (fun j => hσσ (v j))
  change g.val *ᵥ (σ ∘ (g.val *ᵥ (σ ∘ v))) = v
  rw [he, Matrix.mulVec_mulVec, hc, Matrix.one_mulVec]

private theorem twist_form (σ : F ≃+* F) (g : Sp F) (v w : Vector F) :
    form F (twist σ g v) (twist σ g w) = σ (form F v w) := by
  change form F (g • (σ ∘ v)) (g • (σ ∘ w)) = _
  rw [preserves_form]
  simp only [form_apply, Function.comp_apply, map_sum, map_sub, map_mul]

/-- A nontrivial involution of the coefficient field has only symplectic coboundaries. -/
theorem field_cocycle_coboundary [Finite F] (σ : F ≃+* F)
    (hσ : σ ^ 2 = 1) (hσne : σ ≠ 1)
    (g : Sp F) (hg : g * fieldAutomorphism σ g = 1) :
    ∃ h : Sp F, g = h * (fieldAutomorphism σ h)⁻¹ := by
  classical
  let T := twist σ g
  let K := fixedField σ
  let W := fixedSpace σ T (twist_smul σ g)
  let B := fixedForm σ T (twist_smul σ g) (form F) (twist_form σ g)
  have hdim : Module.finrank K W = 2 * 2 := by
    rw [fixedSpace_finrank σ hσne T (twist_smul σ g) (twist_square σ hσ g hg)]
    simp [Vector]
  have hA : B.IsAlt := fixedForm_alt σ T (twist_smul σ g) (form F)
    (twist_form σ g) Matrix.PSp4Three.form_alternating
  have hN : B.Nondegenerate := fixedForm_nondegenerate σ hσne T
    (twist_smul σ g) (twist_square σ hσ g hg) (form F) (twist_form σ g)
    Matrix.PSp4Three.form_alternating Matrix.PSp4Three.form_nondegenerate
  obtain ⟨e⟩ := Matrix.PSp4Three.exists_isometry 2 B hA hN hdim
  let H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
    fun i j => (e.symm (Pi.single j 1)).val i
  have hcol (i j : Fin 2 ⊕ Fin 2) :
      form F (fun k => H k i) (fun k => H k j) = (-Matrix.J (Fin 2) F) i j := by
    have he := congrArg Subtype.val (e.symm.map_app (Pi.single j 1) (Pi.single i 1))
    change form F (fun k => H k i) (fun k => H k j) =
      ((Matrix.PSp4Three.form (Pi.single i 1) (Pi.single j 1) : K) : F) at he
    rw [Matrix.PSp4Three.form, Matrix.toBilin'_single] at he
    rw [he]
    cases i <;> cases j <;> simp [Matrix.J, Matrix.fromBlocks, Matrix.one_apply, apply_ite]
  have hgram : H.transpose * (-Matrix.J (Fin 2) F) * H = -Matrix.J (Fin 2) F := by
    ext i j
    rw [← Matrix.toBilin'_single (H.transpose * (-Matrix.J (Fin 2) F) * H) i j,
      ← Matrix.toBilin'_comp]
    simp only [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply, Matrix.mulVec_single,
      MulOpposite.op_one, one_smul]
    exact hcol i j
  have hH : H ∈ Matrix.symplecticGroup (Fin 2) F := by
    rw [SymplecticGroup.mem_iff']
    simpa only [Matrix.mul_neg, Matrix.neg_mul, neg_inj] using hgram
  let h : Sp F := ⟨H, hH⟩
  refine ⟨h, ?_⟩
  apply (eq_mul_inv_iff_mul_eq).mpr
  apply Subtype.ext
  ext i j
  have he := congrFun (e.symm (Pi.single j 1)).property i
  change (g.val *ᵥ (σ ∘ fun k => H k j)) i = H i j at he
  exact he

/-- The even-degree field involution has trivial symplectic first cohomology. -/
theorem half_frobenius_cocycle_coboundary [Finite F] [CharP F 2] {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : 1 < n) (heven : Even n)
    (g : Sp F) (hg : g * fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)) g = 1) :
    ∃ h : Sp F, g = h * (fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)) h)⁻¹ := by
  have ho : orderOf (frobeniusEquiv F 2 ^ (n / 2)) = 2 := by
    rw [← frobenius_order hcard]
    apply orderOf_pow_orderOf_div
    · rw [frobenius_order hcard]
      omega
    · rw [frobenius_order hcard]
      exact even_iff_two_dvd.mp heven
  apply field_cocycle_coboundary _ _ _ g hg
  · simpa only [ho] using pow_orderOf_eq_one (frobeniusEquiv F 2 ^ (n / 2))
  · intro he
    rw [he, orderOf_one] at ho
    contradiction

/-- The cocycle elimination gives genuine inner conjugacy of the field twist. -/
theorem half_frobenius_twist_isConj [Finite F] [CharP F 2] {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : 1 < n) (heven : Even n)
    (g : Sp F) (hg : g * fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)) g = 1) :
    IsConj (fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)))
      (MulAut.conj g * fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2))) := by
  obtain ⟨h, hh⟩ := half_frobenius_cocycle_coboundary hcard hn heven g hg
  exact inner_twist_isConj _ g h hh

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
