module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.BlockMaps
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.FourSpace

/-!
# Marked determinant-space factors and their exact scalar kernel

Extend the left SL₂ factor by the identity on a nonzero orthogonal complement.
It stays injective and proper after the literal scalar quotient: a scalar that
fixes the complement is one, and the cubic in the right factor is not central.
The commuting right factor and complementary elementary group embed before
projectivization. Their projective kernel is exactly the common square-one
scalar on the two natural spaces, with membership in the complementary Omega
carrier retained. The kernel is central, and the image centralizes the marked
left subgroup. The full-isometry right map is also provided for calculating
that centralizer; it is not identified here with the elementary carrier.

Source: Aschbacher–Smith A.2.17, printed p.39. The literal residual equality
requires a separate centralizer and prime-to-p quotient argument.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.Fundamental.SplitOddBlocks
open Theory.AlgebraicGroup
universe u
variable {F V W : Type u} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

open Matrix FourPlusMatrix

variable (Q : QuadraticForm F V) (S : QuadraticForm F W)
    (e : ((formD 2 F).prod Q).IsometryEquiv S)

/-- The marked left determinant-space factor, extended by the identity. -/
def leftCover : Matrix.SpecialLinearGroup (Fin 2) F →* elementarySubgroup S :=
  (blockMap (formD 2 F) Q S e).comp ((MonoidHom.inl _ _).comp fourLeft)

/-- The commuting right factor and the actual complementary elementary group. -/
def rightCover : Matrix.SpecialLinearGroup (Fin 2) F × elementarySubgroup Q →* elementarySubgroup S :=
  (blockMap (formD 2 F) Q S e).comp (fourRight.prodMap (MonoidHom.id _))

def leftProjective : Matrix.SpecialLinearGroup (Fin 2) F →* ProjectiveElementary S :=
  (projectiveElementaryMap S).comp (leftCover Q S e)

def rightProjective : Matrix.SpecialLinearGroup (Fin 2) F × elementarySubgroup Q →*
    ProjectiveElementary S := (projectiveElementaryMap S).comp (rightCover Q S e)

theorem rightCover_injective : Function.Injective (rightCover Q S e) := by
  intro g h hgh
  have ht : (fourRight g.1, g.2) = (fourRight h.1, h.2) :=
    blockMap_injective _ _ _ e hgh
  exact Prod.ext (fourRight_injective (congrArg Prod.fst ht)) (congrArg (fun z : OmegaPlus 2 F × elementarySubgroup Q => z.2) ht)

theorem leftCover_apply (a : Matrix.SpecialLinearGroup (Fin 2) F) (v : VectorD 2 F × V) :
    (leftCover Q S e a).val.val (e v) = e ((fourLeft a).val.val v.1, v.2) :=
  blockMap_apply _ _ _ _ _ _

theorem rightCover_apply (g : Matrix.SpecialLinearGroup (Fin 2) F × elementarySubgroup Q)
    (v : VectorD 2 F × V) :
    (rightCover Q S e g).val.val (e v) = e ((fourRight g.1).val.val v.1, g.2.val.val v.2) :=
  blockMap_apply _ _ _ _ _ _

theorem factors_commute (a : Matrix.SpecialLinearGroup (Fin 2) F)
    (g : Matrix.SpecialLinearGroup (Fin 2) F × elementarySubgroup Q) :
    Commute (leftCover Q S e a) (rightCover Q S e g) := by
  change Commute (blockMap _ _ _ e (fourLeft a, 1))
    (blockMap _ _ _ e (fourRight g.1, g.2))
  exact (show Commute (fourLeft a, (1 : elementarySubgroup Q)) (fourRight g.1, g.2) from
    Prod.ext (fourFactors_commute a g.1) (by simp)).map (blockMap _ _ _ e)

/-- Projective scalars have the same parameter on both actual summands. -/
theorem block_projective_kernel (g : OmegaPlus 2 F × elementarySubgroup Q) :
    projectiveElementaryMap S (blockMap (formD 2 F) Q S e g) = 1 ↔
      ∃ c : F, c ^ 2 = 1 ∧
        (∀ v, g.1.val.val v = c • v) ∧ (∀ w, g.2.val.val w = c • w) := by
  rw [projectiveElementaryMap_eq_one_iff]
  constructor
  · rintro ⟨c, hc, hs⟩
    have h (v : VectorD 2 F × V) :
        (g.1.val.val v.1, g.2.val.val v.2) = c • v := by
      apply e.injective
      exact (blockMap_apply _ _ _ e g v).symm.trans
        ((hs (e v)).trans (map_smul e c v).symm)
    exact ⟨c, hc, fun v => congrArg Prod.fst (h (v, 0)),
      fun w => congrArg Prod.snd (h (0, w))⟩
  · rintro ⟨c, hc, h1, h2⟩
    refine ⟨c, hc, ?_⟩
    intro w
    obtain ⟨v, rfl⟩ := e.surjective w
    exact (blockMap_apply _ _ _ e g v).trans
      ((congrArg e (Prod.ext (h1 v.1) (h2 v.2))).trans (map_smul e c v))

theorem leftProjective_injective [Nontrivial V] :
    Function.Injective (leftProjective Q S e) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  obtain ⟨c, _, h1, h2⟩ := (block_projective_kernel Q S e (fourLeft a, 1)).mp ha
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hc : c = 1 := smul_left_injective F hv (by simpa using (h2 v).symm)
  have hl : fourLeft a = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    simpa [hc] using h1 w
  exact fourLeft_injective (hl.trans (map_one fourLeft).symm)

private theorem right_scalar_iff (b : Matrix.SpecialLinearGroup (Fin 2) F)
    (c : F) (hc : c ^ 2 = 1) :
    (∀ v, (fourRight b).val.val v = c • v) ↔ b.val = Matrix.scalar (Fin 2) c := by
  have hscalar_square : Matrix.scalar (Fin 2) c * Matrix.scalar (Fin 2) c = 1 := by
    rw [← map_mul, ← pow_two, hc, map_one]
  constructor
  · intro h
    have ht := toOrthogonal_coordinates (1, b) (coordinates.symm 1)
    change coordinates ((fourRight b).val.val (coordinates.symm 1)) = _ at ht
    rw [h, map_smul, LinearEquiv.apply_symm_apply] at ht
    change c • (1 : Mat (F := F)) = (1 : Matrix.SpecialLinearGroup (Fin 2) F).val * 1 * b⁻¹.val at ht
    rw [Matrix.SpecialLinearGroup.coe_one, one_mul, one_mul] at ht
    have hi : b⁻¹.val = Matrix.scalar (Fin 2) c := by
      exact ht.symm.trans (by rw [Matrix.smul_one_eq_diagonal]; rfl)
    have hmul : b⁻¹.val * b.val = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    rw [hi] at hmul
    have heq := congrArg (fun M => Matrix.scalar (Fin 2) c * M) hmul
    simpa only [← mul_assoc, hscalar_square, one_mul, mul_one] using heq
  · intro hb v
    have hs : b * b = 1 := by
      apply Subtype.ext
      change b.val * b.val = (1 : Mat (F := F))
      simpa only [hb] using hscalar_square
    have hi : b⁻¹ = b := inv_eq_of_mul_eq_one_left hs
    apply coordinates.injective
    rw [show coordinates ((fourRight b).val.val v) = coordinates v * b⁻¹.val by
      have ht := toOrthogonal_coordinates (1, b) v
      change coordinates ((fourRight b).val.val v) =
        (1 : Matrix.SpecialLinearGroup (Fin 2) F).val * coordinates v * b⁻¹.val at ht
      simpa only [Matrix.SpecialLinearGroup.coe_one, one_mul] using ht,
      map_smul, hi, hb]
    ext i j
    simp [Matrix.scalar, Matrix.mul_diagonal, mul_comm]

/-- Exact common square-one scalar kernel, with complementary membership retained
by the literal elementary-group argument. -/
theorem rightProjective_kernel (g : Matrix.SpecialLinearGroup (Fin 2) F × elementarySubgroup Q) :
    rightProjective Q S e g = 1 ↔ ∃ c : F, c ^ 2 = 1 ∧
      g.1.val = Matrix.scalar (Fin 2) c ∧ (∀ w, g.2.val.val w = c • w) := by
  change projectiveElementaryMap S (blockMap _ _ _ e (fourRight g.1, g.2)) = 1 ↔ _
  rw [block_projective_kernel]
  exact exists_congr (fun c => and_congr_right (fun hc =>
    and_congr (right_scalar_iff g.1 c hc) Iff.rfl))

/-- The cubic right factor is outside the projective left factor. -/
theorem leftProjective_proper [Nontrivial V] : (leftProjective Q S e).range ≠ ⊤ := by
  intro htop
  obtain ⟨a, ha⟩ := show rightProjective Q S e (cubicSL, 1) ∈ (leftProjective Q S e).range from
    htop ▸ Subgroup.mem_top _
  let f := (projectiveElementaryMap S).comp (blockMap (formD 2 F) Q S e)
  have heq : (fourMap (a⁻¹, cubicSL), (1 : elementarySubgroup Q)) =
      (fourLeft a⁻¹, 1) * (fourRight cubicSL, 1) := by
    exact Prod.ext (fourMap_eq_mul _ _) (one_mul _).symm
  have hker : projectiveElementaryMap S
      (blockMap (formD 2 F) Q S e (fourMap (a⁻¹, cubicSL), 1)) = 1 := by
    change f (fourMap (a⁻¹, cubicSL), 1) = 1
    rw [heq, f.map_mul]
    change leftProjective Q S e a⁻¹ * rightProjective Q S e (cubicSL, 1) = 1
    rw [map_inv, ← ha, inv_mul_cancel]
  obtain ⟨c, _, hs, hc⟩ := (block_projective_kernel Q S e _).mp hker
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hc1 : c = 1 := smul_left_injective F hv (by simpa using (hc v).symm)
  have hf : fourMap (a⁻¹, cubicSL (F := F)) = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    simpa [hc1] using hs w
  obtain ⟨c, _, _, hs⟩ := (fourMap_kernel_scalar _).mp hf
  have hh := congrArg (fun M : Mat (F := F) => M 1 0) hs
  simp [cubicSL, Matrix.scalar, Matrix.diagonal] at hh


/-- Both scalar components are central in their actual carriers. -/
theorem rightProjective_kernel_le_center :
    (rightProjective Q S e).ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F × elementarySubgroup Q) := by
  intro g hg
  obtain ⟨c, hc, h1, h2⟩ := (rightProjective_kernel Q S e g).mp hg
  have hc1 : g.1 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨c, by simpa using hc, h1.symm⟩
  have hc2 : g.2 ∈ Subgroup.center (elementarySubgroup Q) :=
    elementaryScalarSubgroup_le_center Q ⟨c, hc, h2⟩
  rw [Subgroup.mem_center_iff]
  intro h
  exact Prod.ext ((Subgroup.mem_center_iff.mp hc1) h.1) ((Subgroup.mem_center_iff.mp hc2) h.2)

/-- The literal right projective image centralizes the marked left subgroup. -/
theorem rightProjective_range_le_centralizer :
    (rightProjective Q S e).range ≤
      Subgroup.centralizer ((leftProjective Q S e).range : Set (ProjectiveElementary S)) := by
  rintro z ⟨g, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro x ⟨a, rfl⟩
  exact (factors_commute Q S e a g).map (projectiveElementaryMap S)


/-- The same right action with an arbitrary isometry on the complement.
This is used only to describe the full centralizer, before taking its residual. -/
def rightIsometry : Matrix.SpecialLinearGroup (Fin 2) F × quadraticIsometrySubgroup Q →*
    quadraticIsometrySubgroup S :=
  (conjugate e).comp ((orthogonalProd (formD 2 F) Q).comp
    (((elementarySubgroup (formD 2 F)).subtype.comp fourRight).prodMap (MonoidHom.id _)))

theorem rightIsometry_apply (g : Matrix.SpecialLinearGroup (Fin 2) F × quadraticIsometrySubgroup Q)
    (v : VectorD 2 F × V) :
    (rightIsometry Q S e g).val (e v) = e ((fourRight g.1).val.val v.1, g.2.val v.2) := by
  change e ((orthogonalProd (formD 2 F) Q ((fourRight g.1).val, g.2)).val
    (e.symm (e v))) = _
  rw [e.symm_apply_apply]
  rfl

/-- Restricting the complementary isometry to Omega recovers the literal cover. -/
theorem rightIsometry_elementary (g : Matrix.SpecialLinearGroup (Fin 2) F × elementarySubgroup Q) :
    rightIsometry Q S e (g.1, g.2.val) = (rightCover Q S e g).val := rfl

end ClassicalOrthogonal.Fundamental.SplitOddBlocks
