module
public import Theory.Representation.InvariantFormUniqueness
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ModelConjugacy
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.CoefficientNormalizer

/-!
# Symplectic conjugacy from an absolutely irreducible coefficient model

An actual linear intertwiner pulls the target form back to an invariant
nondegenerate form. Absolute irreducibility makes that form a scalar multiple
of the original one; a square-root rescaling over the finite field makes
the intertwiner symplectic. The subgroup application retains the literal
coefficient embedding and the internal ambient conjugating matrix.

This is the change-of-form step in Aschbacher--Smith G.4.1 and G.4.8--9,
printed pp.340--342. It applies to the genuine simple transvection socle:
the rank-one normalizer proves absolute irreducibility even when the
transvection is outside the socle. Classification of the module that
constructs the linear intertwiner remains a separate input.
-/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open Matrix Subgroup
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
open DiagramAutomorphisms.FieldFixedResidual
variable {F G : Type*} [Field F] [Finite F] [CharP F 2] [Group G]

/-- An actual intertwiner between absolutely irreducible symplectic actions
can be rescaled to an internal symplectic conjugating matrix. -/
theorem exists_symplectic_intertwiner_of_absolutelyIrreducible
    (ρ τ : G →* Sp F)
    (habs : Representation.IsAbsolutelyIrreducible
      ((Representation.symplecticNatural 2).comp ρ))
    (A : Vector F ≃ₗ[F] Vector F)
    (hA : ∀ x v, A (ρ x • v) = τ x • A v) :
    ∃ g : Sp F, ∀ x, g * ρ x * g⁻¹ = τ x := by
  let σ : Representation F G (Vector F) := (Representation.symplecticNatural 2).comp ρ
  letI : Representation.IsAbsolutelyIrreducible σ := habs
  letI : Representation.IsIrreducible σ :=
    Representation.IsAbsolutelyIrreducible.irreducible_of_isAbsolutelyIrreducible σ
  let B := (form F).comp A.toLinearMap A.toLinearMap
  have hB : ∀ x v w, B (σ x v) (σ x w) = B v w := by
    intro x v w
    change form F (A (ρ x • v)) (A (ρ x • w)) = form F (A v) (A w)
    rw [hA, hA, preserves_form]
  obtain ⟨c,hc⟩ := Representation.invariant_form_scalar_of_absolutelyIrreducible
    σ (form F) TwoLocalCover.form_nondegenerate (fun x => preserves_form (ρ x)) B hB
  have hmul (v w : Vector F) : form F (A v) (A w) = c * form F v w := by
    exact congrArg (fun C : LinearMap.BilinForm F (Vector F) => C v w) hc
  have hc0 : c ≠ 0 := by
    intro hz
    have h := hmul (A.symm (e 0)) (A.symm (Pi.single (.inr 0) 1))
    simp [hz, form_apply, e, Pi.single_apply] at h
  obtain ⟨a,ha⟩ := Finite.surjective_of_injective (CharTwo.sq_injective (R := F)) c⁻¹
  change a ^ 2 = c⁻¹ at ha
  have hnorm : a * a * c = 1 := by rw [←pow_two,ha,inv_mul_cancel₀ hc0]
  let L : Module.End F (Vector F) := a • A.toLinearMap
  have hL (v w : Vector F) : form F (L v) (L w) = form F v w := by
    change form F (a • A v) (a • A w) = _
    simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,hmul]
    calc
      a * (a * (c * form F v w)) = (a*a*c)*form F v w := by ring
      _ = form F v w := by rw [hnorm,one_mul]
  let g : Sp F := ⟨LinearMap.toMatrix' L, by
    apply SymplecticGroup.mem_iff'.mpr
    have he := Matrix.toBilin'_comp (-Matrix.J (Fin 2) F)
      (LinearMap.toMatrix' L) (LinearMap.toMatrix' L)
    have hpres : (form F).comp L L = form F := by
      apply LinearMap.ext
      intro v
      apply LinearMap.ext
      intro w
      exact hL v w
    simp only [Matrix.toLin'_toMatrix'] at he
    have hm := Matrix.toBilin'.injective (he.symm.trans hpres)
    simpa [Matrix.mul_neg,Matrix.neg_mul,form] using hm⟩
  have hg (v : Vector F) : g • v = a • A v := LinearMap.toMatrix'_mulVec L v
  refine ⟨g,fun x => ?_⟩
  have hinter : g * ρ x = τ x * g := by
    apply Subtype.ext
    ext i j
    have h : (g * ρ x) • (Pi.single j (1 : F) : Vector F) =
        (τ x * g) • (Pi.single j (1 : F) : Vector F) := by
      simp only [mul_smul,hg,hA]
      exact ((toLinear (τ x)).map_smul a (A (Pi.single j (1 : F)))).symm
    exact congrFun (by simpa only [smul_eq_mulVec,Matrix.mulVec_single_one] using h) i
  rw [hinter,mul_assoc,mul_inv_cancel, mul_one]

/-- A literal coefficient model and its intertwiner yield the required
equality with a conjugate of the coefficient-inclusion range. -/
theorem exists_coefficient_conjugator_of_absolute_intertwiner
    (H : Subgroup (Sp F))
    (habs : Representation.IsAbsolutelyIrreducible
      ((Representation.symplecticNatural 2).comp H.subtype))
    (K : Subfield F) (eK : H ≃* Sp K) (A : Vector F ≃ₗ[F] Vector F)
    (hA : ∀ x : H, ∀ v, A ((x : Sp F) • v) = coefficientInclusion K (eK x) • A v) :
    ∃ g : Sp F, H = (coefficientInclusion K).range.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,hg⟩ := exists_symplectic_intertwiner_of_absolutelyIrreducible H.subtype
    ((coefficientInclusion K).comp eK.toMonoidHom) habs A hA
  change ∀ x : H, g * (x : Sp F) * g⁻¹ = coefficientInclusion K (eK x) at hg
  refine ⟨g⁻¹,?_⟩
  ext x
  constructor
  · intro hx
    refine ⟨coefficientInclusion K (eK ⟨x,hx⟩),⟨eK ⟨x,hx⟩,rfl⟩,?_⟩
    change g⁻¹ * coefficientInclusion K (eK ⟨x,hx⟩) * (g⁻¹)⁻¹ = x
    rw [←hg ⟨x,hx⟩]
    simp [mul_assoc]
  · rintro ⟨y,⟨z,rfl⟩,rfl⟩
    obtain ⟨u,rfl⟩ := eK.surjective z
    have he : (MulAut.conj g⁻¹) (coefficientInclusion K (eK u)) = (u : Sp F) := by
      change g⁻¹ * coefficientInclusion K (eK u) * (g⁻¹)⁻¹ = u
      rw [←hg u]
      simp [mul_assoc]
    exact he.symm ▸ u.property

/-- A recognized absolutely irreducible normal layer identifies its full
ambient subgroup, retaining the actual coefficient inclusion. -/
theorem exists_coefficient_conjugator_of_normalized_absolute_intertwiner
    (H N : Subgroup (Sp F)) (hNH : N ≤ H)
    (hH : H ≤ normalizer (N : Set (Sp F)))
    (habs : Representation.IsAbsolutelyIrreducible
      ((Representation.symplecticNatural 2).comp N.subtype))
    (K : Subfield F) (eK : N ≃* Sp K) (A : Vector F ≃ₗ[F] Vector F)
    (hA : ∀ x : N, ∀ v,
      A ((x : Sp F) • v) = coefficientInclusion K (eK x) • A v) :
    ∃ g : Sp F, H = (coefficientInclusion K).range.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,hg⟩ := exists_coefficient_conjugator_of_absolute_intertwiner N habs K eK A hA
  refine ⟨g, le_antisymm ?_ ?_⟩
  · rw [hg, conjugate_coefficient_range_normalizer] at hH
    exact hH
  · rw [←hg]
    exact hNH

end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
