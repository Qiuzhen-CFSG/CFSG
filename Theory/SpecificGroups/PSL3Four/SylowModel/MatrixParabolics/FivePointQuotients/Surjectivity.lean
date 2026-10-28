module

public import Theory.SpecificGroups.PSL3Four.SylowModel.MatrixParabolics.FivePointQuotients.Action
public import Mathlib.GroupTheory.GroupAction.Jordan

/-!
# Surjectivity of the two geometric five-point actions

Each standard parabolic induces the full symmetric group on its incident pencil.
For transitivity, complete any nonzero two-coordinate column to a determinant-one
block matrix. In the first pencil use the inverse transpose of the lower block,
so its covector action is the prescribed block; in the second use the upper block
on points. These matrices belong to the literal point and plane stabilizers.

Coordinate Frobenius fixes the two coordinate points and their sum but moves an
affine point with a coordinate outside the prime field. On a five-element pencil,
this makes its permutation a transposition. Transitivity in prime degree implies
primitivity, and Jordan's transposition theorem identifies the image with S₅.

The exported theorems discharge the surjectivity premises in the separate
`FivePointQuotients` kernel and quotient assembly without importing that module.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, §5.3.2
and the exceptional case of §5.3.7, printed pp. 659--661 (PDF pp. 676--678).
-/

public section

open Matrix Configuration Projectivization
namespace Matrix.PSL3Four.SylowModel.MatrixRealization
noncomputable section

private def base₁ : Pencil₁ :=
  ⟨mk F ![0, 1, 0] (by simp), by simp⟩
private def base₂ : Pencil₂ :=
  ⟨mk F ![1, 0, 0] (by simp), by simp⟩

private theorem complete_column (a b : F) (h : a ≠ 0 ∨ b ≠ 0) :
    ∃ c d : F, a * d - b * c = 1 := by
  by_cases ha : a = 0
  · have hb : b ≠ 0 := h.resolve_left (not_not.mpr ha)
    exact ⟨-b⁻¹, 0, by simp [ha, hb]⟩
  · exact ⟨0, a⁻¹, by simp [ha]⟩

private def block₁ (a b c d : F) (h : a * d - b * c = 1) : SL :=
  ⟨!![1, 0, 0; 0, a, c; 0, b, d], by simpa [Matrix.det_fin_three, mul_comm b c] using h⟩
private def block₂ (a b c d : F) (h : a * d - b * c = 1) : SL :=
  ⟨!![a, c, 0; b, d, 0; 0, 0, 1], by simpa [Matrix.det_fin_three, mul_comm b c] using h⟩

private theorem block₁_fixes (a b c d : F) (h : a * d - b * c = 1) :
    (block₁ a b c d h).transpose • standardPoint = standardPoint := by
  rw [standardPoint, Projectivization.smul_mk]
  congr 1
  change (block₁ a b c d h).val.transpose *ᵥ ![1, 0, 0] = ![1, 0, 0]
  ext i
  fin_cases i <;> simp [block₁, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem block₂_fixes (a b c d : F) (h : a * d - b * c = 1) :
    (block₂ a b c d h).transpose • standardPlane = standardPlane := by
  rw [standardPlane, Projectivization.smul_mk]
  congr 1
  change (block₂ a b c d h).val.transpose *ᵥ ![0, 0, 1] = ![0, 0, 1]
  ext i
  fin_cases i <;> simp [block₂, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem transitive₁ (l : Pencil₁) : ∃ g : parabolic₁, pencilAction₁ g base₁ = l := by
  rcases l with ⟨l, hl⟩
  induction l using Projectivization.ind with | h v hv =>
  have hv0 := (standardPoint_mem_mk v hv).mp hl
  have hn : v 1 ≠ 0 ∨ v 2 ≠ 0 := by
    by_contra! h
    apply hv
    ext i
    fin_cases i <;> simp [hv0, h.1, h.2]
  obtain ⟨c, d, hd⟩ := complete_column (v 1) (v 2) hn
  let B := block₁ (v 1) (v 2) c d hd
  have hB : linearInclusion (((B.transpose)⁻¹ : SL) : PSL) ∈ parabolic₁ := by
    rw [mem_parabolic₁]
    change B.transpose⁻¹ • standardPoint = standardPoint
    rw [inv_smul_eq_iff]
    exact (block₁_fixes _ _ _ _ _).symm
  refine ⟨⟨_, hB⟩, ?_⟩
  apply Subtype.ext
  change SpecialLinearGroup.inverseTranspose (B.transpose)⁻¹ • (base₁ : PG) = mk F v hv
  have he : SpecialLinearGroup.inverseTranspose (B.transpose)⁻¹ = B := by
    change (((B.transpose)⁻¹)⁻¹).transpose = B
    rw [inv_inv]
    rfl
  rw [he]
  change B • mk F ![0, 1, 0] _ = mk F v hv
  rw [Projectivization.smul_mk]
  congr 1
  change B.val *ᵥ ![0, 1, 0] = v
  ext i
  fin_cases i <;> simp [B, block₁, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv0]

private theorem transitive₂ (p : Pencil₂) : ∃ g : parabolic₂, pencilAction₂ g base₂ = p := by
  rcases p with ⟨p, hp⟩
  induction p using Projectivization.ind with | h v hv =>
  have hv2 := (mk_mem_standardPlane v hv).mp hp
  have hn : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra! h
    apply hv
    ext i
    fin_cases i <;> simp [hv2, h.1, h.2]
  obtain ⟨c, d, hd⟩ := complete_column (v 0) (v 1) hn
  let B := block₂ (v 0) (v 1) c d hd
  have hB : linearInclusion (B : PSL) ∈ parabolic₂ := by
    rw [mem_parabolic₂]
    change SpecialLinearGroup.inverseTranspose B • standardPlane = standardPlane
    have hi : (SpecialLinearGroup.inverseTranspose B)⁻¹ • standardPlane = standardPlane := by
      rw [← map_inv]
      change (B⁻¹)⁻¹.transpose • standardPlane = standardPlane
      rw [inv_inv]
      exact block₂_fixes _ _ _ _ _
    exact (inv_smul_eq_iff.mp hi).symm
  refine ⟨⟨_, hB⟩, ?_⟩
  apply Subtype.ext
  change B • mk F ![1, 0, 0] _ = mk F v hv
  rw [Projectivization.smul_mk]
  congr 1
  change B.val *ᵥ ![1, 0, 0] = v
  ext i
  fin_cases i <;> simp [B, block₂, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv2]

-- A nonidentity permutation fixing three of five points is a transposition.
private theorem onto_of_five {G X : Type*} [Group G] [Finite X]
    (ρ : G →* Equiv.Perm X) (hc : Nat.card X = 5)
    (a b c : X) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ht : ∀ x, ∃ g, ρ g a = x) (s : G) (hs : ρ s ≠ 1)
    (ha : ρ s a = a) (hb : ρ s b = b) (hc' : ρ s c = c) :
    Function.Surjective ρ := by
  classical
  let := Fintype.ofFinite X
  have hsup : (ρ s).support ⊆ Finset.univ \ {a, b, c} := by
    intro x hx
    simp only [Equiv.Perm.mem_support] at hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    exact ⟨fun h => hx (h ▸ ha), fun h => hx (h ▸ hb), fun h => hx (h ▸ hc')⟩
  have hup := Finset.card_le_card hsup
  have hlow := Equiv.Perm.two_le_card_support_of_ne_one hs
  have hcard : Fintype.card X = 5 := by rwa [← Nat.card_eq_fintype_card]
  have hswap : Equiv.Perm.IsSwap (ρ s) := by
    apply Equiv.Perm.card_support_eq_two.mp
    simp [Finset.card_sdiff, hcard, hab, hac, hbc] at hup
    exact le_antisymm hup hlow
  have : MulAction.IsPretransitive ρ.range X := by
    rw [MulAction.isPretransitive_iff_base a]
    intro x
    obtain ⟨g, hg⟩ := ht x
    exact ⟨⟨ρ g, g, rfl⟩, hg⟩
  apply MonoidHom.range_eq_top.mp
  exact Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem
    (MulAction.IsPreprimitive.of_prime_card (by rw [hc]; decide)) (ρ s) hswap ⟨s, rfl⟩

private def affine₁ (x : F) : Pencil₁ :=
  ⟨mk F ![0, 1, x] (by simp), by simp⟩
private def affine₂ (x : F) : Pencil₂ :=
  ⟨mk F ![1, x, 0] (by simp), by simp⟩
private def infinity₁ : Pencil₁ :=
  ⟨mk F ![0, 0, 1] (by simp), by simp⟩
private def infinity₂ : Pencil₂ :=
  ⟨mk F ![0, 1, 0] (by simp), by simp⟩

private theorem affine₁_injective : Function.Injective affine₁ := by
  intro x y he
  have he' := congrArg Subtype.val he
  obtain ⟨u, hu⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp he'
  have hu1 := congrFun hu 1
  have hu2 := congrFun hu 2
  change (u : F) * 1 = 1 at hu1
  change (u : F) * y = x at hu2
  simp only [mul_one] at hu1
  simpa [hu1] using hu2.symm

private theorem affine₂_injective : Function.Injective affine₂ := by
  intro x y he
  have he' := congrArg Subtype.val he
  obtain ⟨u, hu⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp he'
  have hu0 := congrFun hu 0
  have hu1 := congrFun hu 1
  change (u : F) * 1 = 1 at hu0
  change (u : F) * y = x at hu1
  simp only [mul_one] at hu0
  simpa [hu0] using hu1.symm

private theorem affine₁_ne_infinity (x : F) : affine₁ x ≠ infinity₁ := by
  intro he
  obtain ⟨u, hu⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp (congrArg Subtype.val he)
  have hu1 := congrFun hu 1
  change (u : F) * 0 = 1 at hu1
  simp at hu1

private theorem affine₂_ne_infinity (x : F) : affine₂ x ≠ infinity₂ := by
  intro he
  obtain ⟨u, hu⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp (congrArg Subtype.val he)
  have hu0 := congrFun hu 0
  change (u : F) * 0 = 1 at hu0
  simp at hu0

private def fieldElement₁ : parabolic₁ :=
  ⟨fieldInclusion (Multiplicative.ofAdd (1 : ZMod 2)), by
    rw [mem_parabolic₁]
    change Collineation.pointHom PG PG
      (pairedAction (fieldInclusion (Multiplicative.ofAdd (1 : ZMod 2)))) standardPoint = _
    rw [pairedAction_field_point, frobenius_standardPoint]⟩
private def fieldElement₂ : parabolic₂ :=
  ⟨fieldInclusion (Multiplicative.ofAdd (1 : ZMod 2)), by
    rw [mem_parabolic₂]
    change Collineation.lineHom PG PG
      (pairedAction (fieldInclusion (Multiplicative.ofAdd (1 : ZMod 2)))) standardPlane = _
    rw [pairedAction_field_line, frobenius_standardPlane]⟩

private theorem field_apply₁ (l : Pencil₁) :
    (pencilAction₁ fieldElement₁ l).val = projectiveFrobenius l.val := by
  change Collineation.lineHom PG PG
    (pairedAction (fieldInclusion (Multiplicative.ofAdd (1 : ZMod 2)))) l.val = _
  exact pairedAction_field_line _

private theorem field_apply₂ (p : Pencil₂) :
    (pencilAction₂ fieldElement₂ p).val = projectiveFrobenius p.val := by
  change Collineation.pointHom PG PG
    (pairedAction (fieldInclusion (Multiplicative.ofAdd (1 : ZMod 2)))) p.val = _
  exact pairedAction_field_point _

private theorem field_affine₁ (x : F) :
    pencilAction₁ fieldElement₁ (affine₁ x) = affine₁ (fieldFrobenius x) := by
  apply Subtype.ext
  rw [field_apply₁]
  change projectiveFrobenius (mk F ![0, 1, x] _) = mk F ![0, 1, fieldFrobenius x] _
  rw [projectiveFrobenius_mk]
  congr 1
  ext i
  fin_cases i <;> simp

private theorem field_affine₂ (x : F) :
    pencilAction₂ fieldElement₂ (affine₂ x) = affine₂ (fieldFrobenius x) := by
  apply Subtype.ext
  rw [field_apply₂]
  change projectiveFrobenius (mk F ![1, x, 0] _) = mk F ![1, fieldFrobenius x, 0] _
  rw [projectiveFrobenius_mk]
  congr 1
  ext i
  fin_cases i <;> simp

private theorem field_infinity₁ : pencilAction₁ fieldElement₁ infinity₁ = infinity₁ := by
  apply Subtype.ext
  rw [field_apply₁]
  change projectiveFrobenius standardPlane = standardPlane
  exact frobenius_standardPlane

private theorem field_infinity₂ : pencilAction₂ fieldElement₂ infinity₂ = infinity₂ := by
  apply Subtype.ext
  rw [field_apply₂]
  change projectiveFrobenius (mk F ![0, 1, 0] _) = mk F ![0, 1, 0] _
  rw [projectiveFrobenius_mk]
  congr 1
  ext i
  fin_cases i <;> simp

private theorem field_ne_one₁ : pencilAction₁ fieldElement₁ ≠ 1 := by
  intro he
  obtain ⟨x, hx⟩ := exists_fieldFrobenius_ne
  apply hx
  apply affine₁_injective
  rw [← field_affine₁, he]
  rfl

private theorem field_ne_one₂ : pencilAction₂ fieldElement₂ ≠ 1 := by
  intro he
  obtain ⟨x, hx⟩ := exists_fieldFrobenius_ne
  apply hx
  apply affine₂_injective
  rw [← field_affine₂, he]
  rfl

/-- The actual point stabilizer induces every permutation of its five incident lines. -/
theorem fivePointAction₁_surjective : Function.Surjective fivePointAction₁ := by
  apply fivePointAction₁_surjective_iff.mpr
  apply onto_of_five pencilAction₁ card_pencil₁ (affine₁ 0) infinity₁ (affine₁ 1)
    (affine₁_ne_infinity 0) (affine₁_injective.ne zero_ne_one)
    (affine₁_ne_infinity 1).symm transitive₁ fieldElement₁ field_ne_one₁
  · simpa using field_affine₁ 0
  · exact field_infinity₁
  · simpa using field_affine₁ 1

/-- The actual plane stabilizer induces every permutation of its five incident points. -/
theorem fivePointAction₂_surjective : Function.Surjective fivePointAction₂ := by
  apply fivePointAction₂_surjective_iff.mpr
  apply onto_of_five pencilAction₂ card_pencil₂ (affine₂ 0) infinity₂ (affine₂ 1)
    (affine₂_ne_infinity 0) (affine₂_injective.ne zero_ne_one)
    (affine₂_ne_infinity 1).symm transitive₂ fieldElement₂ field_ne_one₂
  · simpa using field_affine₂ 0
  · exact field_infinity₂
  · simpa using field_affine₂ 1

end
end Matrix.PSL3Four.SylowModel.MatrixRealization
