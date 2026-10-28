module

public import Theory.SpecificGroups.PSL3Four.SylowModel.MatrixParabolics.FivePointQuotients.Action
public import Theory.SpecificGroups.PSL3Four.SylowModel.MatrixParabolics.FivePointQuotients.Surjectivity

/-!
# Quotient assembly from the geometric five-point actions

A surjective five-point action of either parabolic has kernel of order 16,
because the parabolic has order 1920. Its contained root plane also has order
16, so the kernel is exactly that root plane. This proves relative normality
and gives an actual quotient multiplicative equivalence induced by the action.

The imported surjectivity proofs use the actual block-matrix and Frobenius
actions on the pencils. Applying them here discharges every premise of the
kernel calculation and constructs both S₅ quotient equivalences. The formulas
on quotient representatives retain their connection to the geometric actions.
The conditional assembly results are preserved for compatibility.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, §5.3.2
and the exceptional case of §5.3.7, printed pp. 659--661 (PDF pp. 676--678).
-/

@[expose] public section
noncomputable section
namespace Matrix.PSL3Four.SylowModel.MatrixRealization

private theorem card_ker_of_surjective {G : Type*} [Group G]
    (f : G →* Equiv.Perm (Fin 5)) (hG : Nat.card G = 1920)
    (hf : Function.Surjective f) : Nat.card f.ker = 16 := by
  have h := f.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf, Subgroup.card_top, hG] at h
  have hc : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  rw [hc] at h
  omega

/-- Once the geometric action is onto, its kernel is precisely the first root plane. -/
theorem ker_fivePointAction₁_of_surjective (h : Function.Surjective fivePointAction₁) :
    fivePointAction₁.ker = rootPlane₁.subgroupOf parabolic₁ := by
  symm
  apply Subgroup.eq_of_le_of_card_ge rootPlane₁_le_ker_fivePointAction₁
  rw [card_ker_of_surjective fivePointAction₁ card_parabolic₁ h,
    card_rootPlane₁_subgroupOf_parabolic₁]

/-- Once the geometric action is onto, its kernel is precisely the second root plane. -/
theorem ker_fivePointAction₂_of_surjective (h : Function.Surjective fivePointAction₂) :
    fivePointAction₂.ker = rootPlane₂.subgroupOf parabolic₂ := by
  symm
  apply Subgroup.eq_of_le_of_card_ge rootPlane₂_le_ker_fivePointAction₂
  rw [card_ker_of_surjective fivePointAction₂ card_parabolic₂ h,
    card_rootPlane₂_subgroupOf_parabolic₂]

theorem rootPlane₁_normal_parabolic₁_of_surjective (h : Function.Surjective fivePointAction₁) :
    (rootPlane₁.subgroupOf parabolic₁).Normal := by
  rw [← ker_fivePointAction₁_of_surjective h]
  infer_instance

theorem rootPlane₂_normal_parabolic₂_of_surjective (h : Function.Surjective fivePointAction₂) :
    (rootPlane₂.subgroupOf parabolic₂).Normal := by
  rw [← ker_fivePointAction₂_of_surjective h]
  infer_instance

/-- The first actual quotient equivalence; surjectivity remains an explicit input. -/
def parabolicQuotientEquiv₁OfSurjective (h : Function.Surjective fivePointAction₁) :
    letI := rootPlane₁_normal_parabolic₁_of_surjective h
    parabolic₁ ⧸ rootPlane₁.subgroupOf parabolic₁ ≃* Equiv.Perm (Fin 5) := by
  letI := rootPlane₁_normal_parabolic₁_of_surjective h
  exact (QuotientGroup.quotientMulEquivOfEq (ker_fivePointAction₁_of_surjective h).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective fivePointAction₁ h)

/-- The second actual quotient equivalence; surjectivity remains an explicit input. -/
def parabolicQuotientEquiv₂OfSurjective (h : Function.Surjective fivePointAction₂) :
    letI := rootPlane₂_normal_parabolic₂_of_surjective h
    parabolic₂ ⧸ rootPlane₂.subgroupOf parabolic₂ ≃* Equiv.Perm (Fin 5) := by
  letI := rootPlane₂_normal_parabolic₂_of_surjective h
  exact (QuotientGroup.quotientMulEquivOfEq (ker_fivePointAction₂_of_surjective h).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective fivePointAction₂ h)

/-- The kernel of the action on lines through the standard point is its root plane. -/
theorem ker_fivePointAction₁ :
    fivePointAction₁.ker = rootPlane₁.subgroupOf parabolic₁ :=
  ker_fivePointAction₁_of_surjective fivePointAction₁_surjective

/-- The kernel of the action on points of the standard plane is its root plane. -/
theorem ker_fivePointAction₂ :
    fivePointAction₂.ker = rootPlane₂.subgroupOf parabolic₂ :=
  ker_fivePointAction₂_of_surjective fivePointAction₂_surjective

/-- Relative normality in the actual point stabilizer. -/
instance rootPlane₁_normal_parabolic₁ : (rootPlane₁.subgroupOf parabolic₁).Normal :=
  rootPlane₁_normal_parabolic₁_of_surjective fivePointAction₁_surjective

/-- Relative normality in the actual plane stabilizer. -/
instance rootPlane₂_normal_parabolic₂ : (rootPlane₂.subgroupOf parabolic₂).Normal :=
  rootPlane₂_normal_parabolic₂_of_surjective fivePointAction₂_surjective

/-- The point parabolic modulo its root plane is S₅, via its five incident lines. -/
def parabolicQuotientEquiv₁ :
    parabolic₁ ⧸ rootPlane₁.subgroupOf parabolic₁ ≃* Equiv.Perm (Fin 5) :=
  parabolicQuotientEquiv₁OfSurjective fivePointAction₁_surjective

/-- The plane parabolic modulo its root plane is S₅, via its five incident points. -/
def parabolicQuotientEquiv₂ :
    parabolic₂ ⧸ rootPlane₂.subgroupOf parabolic₂ ≃* Equiv.Perm (Fin 5) :=
  parabolicQuotientEquiv₂OfSurjective fivePointAction₂_surjective

/-- The first quotient equivalence induces the original geometric action. -/
@[simp] theorem parabolicQuotientEquiv₁_mk (g : parabolic₁) :
    parabolicQuotientEquiv₁ (QuotientGroup.mk' (rootPlane₁.subgroupOf parabolic₁) g) =
      fivePointAction₁ g := rfl

/-- The second quotient equivalence induces the original geometric action. -/
@[simp] theorem parabolicQuotientEquiv₂_mk (g : parabolic₂) :
    parabolicQuotientEquiv₂ (QuotientGroup.mk' (rootPlane₂.subgroupOf parabolic₂) g) =
      fivePointAction₂ g := rfl

end Matrix.PSL3Four.SylowModel.MatrixRealization
