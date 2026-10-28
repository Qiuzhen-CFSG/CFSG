module

public import Theory.SpecificGroups.SymplecticFour.LocalFactors
import Mathlib.Tactic.FinCases
/-!
# Coordinates on the determinant kernels of the Sp₄ flag

The determinant on the standard point is the first diagonal entry. On the
plane it is the determinant of the upper-left two-by-two block. Consequently
the intersection of the two local factors consists precisely of the Borel
matrices whose first two diagonal entries are one. The explicit diagonal torus
surjects onto both determinant characters, proving the two parabolic join
identities. A nontrivial torus scalar separates the Borel from the unipotent
subgroup whenever the finite field has more than two elements.

Source: the standard matrix flag realization underlying Aschbacher--Smith,
F.1.12(I)(2), printed pp.262--264.
-/

@[expose] public section
namespace Theory.SpecificGroups.SymplecticFour
open Matrix
variable {F : Type*} [Field F]
noncomputable section

/-- Coordinates on the standard point, using its first entry. -/
def pointEquiv : point F ≃ₗ[F] F where
  toFun x := x.val (.inl 0)
  invFun a := ⟨a • e 0, Submodule.smul_mem _ a (Submodule.subset_span (by simp))⟩
  left_inv x := by
    apply Subtype.ext
    change x.val (.inl 0) • e 0 = x.val
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp x.property
    rw [← ha]
    simp [e]
  right_inv a := by simp [e]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma point_determinant (g : stabilizer (point F)) :
    (determinantCharacter (point F) g : F) = g.val.val (.inl 0) (.inl 0) := by
  change (LinearEquiv.det (restriction (point F) g) : F) = _
  rw [LinearEquiv.coe_det]
  rw [← LinearMap.det_conj _ pointEquiv]
  have h : pointEquiv.toLinearMap ∘ₗ (restriction (point F) g).toLinearMap ∘ₗ
      pointEquiv.symm.toLinearMap =
      g.val.val (.inl 0) (.inl 0) • (LinearMap.id : F →ₗ[F] F) := by
    apply LinearMap.ext
    intro x
    simp [pointEquiv, restriction_apply, smul_eq_mulVec, e, mulVec_smul, mulVec_single,
      mul_comm]
  rw [h, LinearMap.det_smul]
  simp

lemma plane_determinant (g : stabilizer (plane F)) :
    (determinantCharacter (plane F) g : F) =
      g.val.val (.inl 0) (.inl 0) * g.val.val (.inl 1) (.inl 1) -
      g.val.val (.inl 0) (.inl 1) * g.val.val (.inl 1) (.inl 0) := by
  change (LinearEquiv.det (restriction (plane F) g) : F) = _
  rw [LinearEquiv.coe_det]
  rw [← LinearMap.det_conj _ planeEquiv]
  have h : planeEquiv.toLinearMap ∘ₗ (restriction (plane F) g).toLinearMap ∘ₗ
      planeEquiv.symm.toLinearMap =
      Matrix.toLin' (g.val.val.submatrix Sum.inl Sum.inl) := by
    apply LinearMap.ext
    intro x
    funext i
    change (g.val.val *ᵥ Sum.elim x 0) (.inl i) =
      (g.val.val.submatrix Sum.inl Sum.inl *ᵥ x) i
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.submatrix]
  rw [h, LinearMap.det_toLin', Matrix.det_fin_two]
  rfl

lemma mem_determinantKernel_iff (W : Submodule F (Vector F)) (g : Sp F) :
    g ∈ determinantKernel W ↔ ∃ hg : g ∈ stabilizer W,
      determinantCharacter W ⟨g, hg⟩ = 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

lemma mem_pointLocal_iff (g : Sp F) :
    g ∈ pointLocal ↔ g ∈ pointParabolic ∧ g.val (.inl 0) (.inl 0) = 1 := by
  rw [pointLocal, mem_determinantKernel_iff]
  constructor
  · rintro ⟨hg, h⟩
    exact ⟨hg, by simpa [point_determinant] using congrArg Units.val h⟩
  · rintro ⟨hg, h⟩
    refine ⟨hg, Units.ext ?_⟩
    simpa [point_determinant] using h

lemma mem_planeLocal_iff (g : Sp F) :
    g ∈ planeLocal ↔ g ∈ planeParabolic ∧
      g.val (.inl 0) (.inl 0) * g.val (.inl 1) (.inl 1) -
      g.val (.inl 0) (.inl 1) * g.val (.inl 1) (.inl 0) = 1 := by
  rw [planeLocal, mem_determinantKernel_iff]
  constructor
  · rintro ⟨hg, h⟩
    exact ⟨hg, by simpa [plane_determinant] using congrArg Units.val h⟩
  · rintro ⟨hg, h⟩
    refine ⟨hg, Units.ext ?_⟩
    simpa [plane_determinant] using h

lemma mem_unipotent_iff (g : Sp F) :
    g ∈ unipotent ↔ g ∈ borel ∧
      g.val (.inl 0) (.inl 0) = 1 ∧ g.val (.inl 1) (.inl 1) = 1 := by
  change (g ∈ pointLocal ∧ g ∈ planeLocal) ↔ _
  rw [mem_pointLocal_iff, mem_planeLocal_iff]
  constructor
  · rintro ⟨⟨hp, h₀⟩, ⟨hl, h₁⟩⟩
    refine ⟨⟨hp, hl⟩, h₀, ?_⟩
    simpa [h₀, (mem_pointParabolic_iff g).mp hp |>.1] using h₁
  · rintro ⟨⟨hp, hl⟩, h₀, h₁⟩
    exact ⟨⟨hp, h₀⟩, ⟨hl, by simp [h₀, h₁, (mem_pointParabolic_iff g).mp hp |>.1]⟩⟩
/-- The diagonal symplectic torus, with inverse scalars on the dual half. -/
def diagonalTorus (a b : Fˣ) : Sp F :=
  ⟨Matrix.diagonal (Sum.elim ![(a : F), (b : F)] ![(↑a⁻¹ : F), (↑b⁻¹ : F)]), by
    rw [SymplecticGroup.mem_iff]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.J, Matrix.fromBlocks, Matrix.mul_apply, Matrix.diagonal]⟩

lemma diagonalTorus_mem_borel (a b : Fˣ) : diagonalTorus a b ∈ borel := by
  simp [mem_borel_iff, diagonalTorus, Matrix.diagonal]

lemma diagonalTorus_point_character (a b : Fˣ) :
    determinantCharacter (point F)
      ⟨diagonalTorus a b, (diagonalTorus_mem_borel a b).1⟩ = a := by
  apply Units.ext
  rw [point_determinant]
  simp [diagonalTorus, Matrix.diagonal]

lemma diagonalTorus_plane_character (a b : Fˣ) :
    determinantCharacter (plane F)
      ⟨diagonalTorus a b, (diagonalTorus_mem_borel a b).2⟩ = a * b := by
  apply Units.ext
  rw [plane_determinant]
  simp [diagonalTorus, Matrix.diagonal]

private lemma stabilizer_eq_kernel_sup (W : Submodule F (Vector F))
    (B : Subgroup (Sp F)) (hB : B ≤ stabilizer W)
    (hlift : ∀ a : Fˣ, ∃ b : B,
      determinantCharacter W ⟨b.val, hB b.property⟩ = a) :
    stabilizer W = determinantKernel W ⊔ B := by
  apply le_antisymm _ (sup_le (determinantKernel_le W) hB)
  intro g hg
  obtain ⟨b, hb⟩ := hlift (determinantCharacter W ⟨g, hg⟩)
  let x : stabilizer W := ⟨g, hg⟩ * ⟨b.val, hB b.property⟩⁻¹
  have hx : x.val ∈ determinantKernel W := by
    refine (mem_determinantKernel_iff W x.val).mpr ⟨x.property, ?_⟩
    change determinantCharacter W x = 1
    simp [x, hb]
  have h := (determinantKernel W ⊔ B).mul_mem
    (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right b.property)
  simpa [x] using h

/-- The point parabolic is generated by its determinant kernel and the whole Borel. -/
lemma pointParabolic_eq_pointLocal_sup_borel :
    pointParabolic (F := F) = pointLocal ⊔ borel := by
  apply stabilizer_eq_kernel_sup (point F) borel inf_le_left
  intro a
  exact ⟨⟨diagonalTorus a 1, diagonalTorus_mem_borel a 1⟩,
    diagonalTorus_point_character a 1⟩

/-- The plane parabolic is generated by its determinant kernel and the whole Borel. -/
lemma planeParabolic_eq_planeLocal_sup_borel :
    planeParabolic (F := F) = planeLocal ⊔ borel := by
  apply stabilizer_eq_kernel_sup (plane F) borel inf_le_right
  intro a
  refine ⟨⟨diagonalTorus a 1, diagonalTorus_mem_borel a 1⟩, ?_⟩
  simpa using diagonalTorus_plane_character a 1

lemma unipotent_ne_borel [Finite F] (hF : 2 < Nat.card F) :
    unipotent (F := F) ≠ borel := by
  have hc : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  have : Nontrivial Fˣ := (Finite.one_lt_card_iff_nontrivial).mp hc
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  intro h
  have ht := diagonalTorus_mem_borel a 1
  rw [← h, mem_unipotent_iff] at ht
  apply ha
  apply Units.ext
  simpa [diagonalTorus, Matrix.diagonal] using ht.2.1

end
end Theory.SpecificGroups.SymplecticFour
