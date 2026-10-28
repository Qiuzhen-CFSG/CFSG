module
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.Extension
public import Theory.SpecificGroups.SymplecticFour.NaturalScalarCubic
public import Theory.SpecificGroups.SL2.Affine.Action

/-!
# The natural quotient at a symplectic plane parabolic

A nonzero invariant additive subgroup inside the distinguished plane is the
whole plane: the actual SL₂ Levi is transitive on its nonzero vectors. This
does not assume closure under defining-field scalars. On the quotient of the
four-space by this plane the action is contragredient. In characteristic two,
swapping its two coordinates gives the literal natural action of quotientMap.

Source: Aschbacher–Smith C.4.1(2) and original 4.3.7, printed pp.151 and616;
the explicit local matrices are those of F.1.12(I)(2), pp.262–264.
-/

@[expose] public section
noncomputable section
open Matrix Subgroup
namespace Theory.SpecificGroups.SymplecticFour.PlaneNatural
variable {F : Type*} [Field F]

/-- Irreducibility holds for additive subgroups, without a scalar-closure premise. -/
theorem invariant_additive_eq_plane (W : AddSubgroup (Vector F))
    (hne : W ≠ ⊥) (hle : ∀ v ∈ W, v ∈ plane F)
    (hinv : ∀ g ∈ planeLocal, ∀ v ∈ W, g.val.mulVec v ∈ W) :
    W = (plane F).toAddSubgroup := by
  apply le_antisymm hle
  obtain ⟨v,hv,hv0⟩ := W.bot_or_exists_ne_zero.resolve_left hne
  have hvp : ∀ i, v (.inr i) = 0 := hle v hv
  have hvtop : (fun i => v (.inl i)) ≠ 0 := by
    intro he
    apply hv0
    funext i
    cases i with
    | inl i => exact congrFun he i
    | inr i => exact hvp i
  intro w hw
  change ∀ i, w (.inr i) = 0 at hw
  by_cases hw0 : w = 0
  · simpa only [hw0] using W.zero_mem
  have hwtop : (fun i => w (.inl i)) ≠ 0 := by
    intro he
    apply hw0
    funext i
    cases i with
    | inl i => exact congrFun he i
    | inr i => exact hw i
  obtain ⟨a,ha⟩ := Matrix.SL2.exists_mulVec_eq F _ _ hvtop hwtop
  have he : (Plane.levi a).val.val.mulVec v = w := by
    funext i
    cases i with
    | inl i =>
      simpa [Plane.levi_matrix, mulVec, dotProduct, Fintype.sum_sum_type,
        Matrix.fromBlocks] using congrFun ha i
    | inr i =>
      simp [Plane.levi_matrix, mulVec, dotProduct, Fintype.sum_sum_type,
        Matrix.fromBlocks, hvp, hw]
  exact he ▸ hinv (Plane.levi a).val (Plane.levi a).property v hv

/-- The alternating pairing turns the dual quotient into the original natural module. -/
def quotient : Vector F →ₗ[F] (Fin 2 → F) where
  toFun v := ![v (.inr 1), v (.inr 0)]
  map_add' v w := by ext i; fin_cases i <;> rfl
  map_smul' a v := by ext i; fin_cases i <;> rfl

theorem quotient_surjective : Function.Surjective (quotient (F := F)) := by
  intro v
  refine ⟨Sum.elim 0 ![v 1,v 0],?_⟩
  ext i
  fin_cases i <;> rfl

theorem quotient_eq_zero (v : Vector F) : quotient v = 0 ↔ v ∈ plane F := by
  constructor
  · intro h i
    fin_cases i
    · exact congrFun h 1
    · exact congrFun h 0
  · intro h
    ext i
    fin_cases i
    · exact h 1
    · exact h 0

variable [CharP F 2]

/-- Equivariance uses exactly the original plane-local quotient map. -/
theorem quotient_action (g : planeLocal (F := F)) (v : Vector F) :
    quotient (g.val.val.mulVec v) = (Plane.quotientMap g).val.mulVec (quotient v) := by
  have hD : g.val.val.toBlocks₂₂ = ((Plane.quotientMap g)⁻¹).valᵀ := by
    have h := Plane.local_pairing g
    have he : ((Plane.quotientMap g)⁻¹).valᵀ * g.val.val.toBlocks₁₁ᵀ = 1 := by
      rw [← Matrix.transpose_mul]
      change ((Plane.quotientMap g).val * ((Plane.quotientMap g)⁻¹).val)ᵀ = 1
      have hh := congrArg (fun a : SpecialLinearGroup (Fin 2) F => a.val)
        (mul_inv_cancel (Plane.quotientMap g))
      exact (congrArg Matrix.transpose hh).trans transpose_one
    calc
      _ = 1 * g.val.val.toBlocks₂₂ := (one_mul _).symm
      _ = (((Plane.quotientMap g)⁻¹).valᵀ * g.val.val.toBlocks₁₁ᵀ) *
          g.val.val.toBlocks₂₂ := by rw [he]
      _ = _ := by rw [Matrix.mul_assoc,h,mul_one]
  have hC := (mem_planeParabolic_iff g.val).mp (planeLocal_le g.property)
  have hbottom (i : Fin 2) : (g.val.val.mulVec v) (.inr i) =
      (((Plane.quotientMap g)⁻¹).valᵀ).mulVec (fun j => v (.inr j)) i := by
    have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) F =>
      A.mulVec (fun j => v (.inr j)) i) hD
    simpa [mulVec, dotProduct, Fintype.sum_sum_type, hC, Matrix.toBlocks₂₂] using he
  ext i
  fin_cases i <;>
    change (g.val.val.mulVec v) (.inr _) = _
  all_goals rw [hbottom]
  all_goals
    simp [quotient, Matrix.adjugate_fin_two,
      Matrix.transpose_apply, mulVec, dotProduct, Fin.sum_univ_two, CharTwo.neg_eq,
      Plane.quotientMap_val, add_comm]

end Theory.SpecificGroups.SymplecticFour.PlaneNatural
