module
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCoordinates
public import Theory.SpecificGroups.SL2.Affine.Action
public import Mathlib.Tactic.FinCases

/-!
# Natural and dual constituents at an SL₃ point residual

The literal lower-right block of the point stabilizer gives its quotient
onto SL₂. The natural three-space has a central line and this natural
quotient. The dual three-space has a natural annihilator plane, identified
by the alternating form through the same block map, and a central quotient.
The common plane is irreducible even among arbitrary additive subgroups.

These coordinates are used on the original L₁ and its cubic-normalizer
residual in Aschbacher--Smith 11.1.2, printed pp.763--764. They do not assert
that every constituent of a larger ambient two-group is of these types.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Subgroup
open scoped MatrixGroups
namespace Representation.SL3PointConstituents
variable (F : Type*) [Field F]
open Matrix.PSL3.LinearThree

def pointProjection : pointLocalSL F →* SL(2,F) :=
  (SemidirectProduct.rightHom : Matrix.SL2.Affine F →* SL(2,F)).comp
    (pointLocalAffineEquiv F).toMonoidHom

theorem pointProjection_surjective : Function.Surjective (pointProjection F) := by
  intro g
  exact ⟨(pointLocalAffineEquiv F).symm (SemidirectProduct.inr g),by
    change (pointLocalAffineEquiv F ((pointLocalAffineEquiv F).symm _)).right = g
    rw [MulEquiv.apply_symm_apply]
    rfl⟩

def tail : (Fin 3 → F) →ₗ[F] (Fin 2 → F) where
  toFun v := ![v 1,v 2]
  map_add' v w := by ext i; fin_cases i <;> rfl
  map_smul' c v := by ext i; fin_cases i <;> rfl

def dualEmbedding : (Fin 2 → F) →ₗ[F] (Fin 3 → F) where
  toFun v := ![0,v 1,v 0]
  map_add' v w := by ext i; fin_cases i <;> simp
  map_smul' c v := by ext i; fin_cases i <;> simp

theorem tail_surjective : Function.Surjective (tail F) := by
  intro v
  exact ⟨![0,v 0,v 1],by ext i; fin_cases i <;> rfl⟩

theorem dualEmbedding_injective : Function.Injective (dualEmbedding F) := by
  intro v w h
  ext i
  fin_cases i
  · exact congrFun h 2
  · exact congrFun h 1

variable [CharP F 2]

/-- The natural quotient uses the actual lower-right SL₂ block. -/
theorem natural_quotient (g : pointLocalSL F) (v : Fin 3 → F) :
    tail F (g.val.val *ᵥ v) = (pointProjection F g).val *ᵥ tail F v := by
  have hg := (mem_pointLocalSL_iff F g.val).mp g.property
  change tail F (g.val.val *ᵥ v) = (pointLocalAffineEquiv F g).right.val *ᵥ tail F v
  rw [pointLocalAffineEquiv_right_val]
  ext i
  fin_cases i <;> simp [tail,mulVec,dotProduct,Fin.sum_univ_three,Fin.sum_univ_two,hg.2.1,hg.2.2]

/-- The dual annihilator is natural through the very same quotient map. -/
theorem dual_submodule (g : pointLocalSL F) (v : Fin 2 → F) :
    g.val⁻¹.val.transpose *ᵥ dualEmbedding F v =
      dualEmbedding F ((pointProjection F g).val *ᵥ v) := by
  have hg := (mem_pointLocalSL_iff F g.val).mp g.property
  change g.val⁻¹.val.transpose *ᵥ dualEmbedding F v =
    dualEmbedding F ((pointLocalAffineEquiv F g).right.val *ᵥ v)
  rw [pointLocalAffineEquiv_right_val]
  change (Matrix.adjugate g.val.val).transpose *ᵥ _ = _
  rw [adjugate_fin_three]
  ext i
  fin_cases i <;> simp [dualEmbedding,mulVec,dotProduct,Fin.sum_univ_three,
    Fin.sum_univ_two,hg.1,hg.2.1,hg.2.2,CharTwo.neg_eq,add_comm]

omit [CharP F 2] in
theorem dual_range (v : Fin 3 → F) : v ∈ (dualEmbedding F).range ↔ v 0 = 0 := by
  constructor
  · rintro ⟨w,rfl⟩; rfl
  · intro h
    refine ⟨![v 2,v 1],?_⟩
    ext i
    fin_cases i <;> simp [dualEmbedding,h]

omit [CharP F 2] in
/-- The natural line is central for the point residual. -/
theorem natural_line_fixed (g : pointLocalSL F) (c : F) :
    g.val.val *ᵥ ![c,0,0] = ![c,0,0] := by
  have hg := (mem_pointLocalSL_iff F g.val).mp g.property
  ext i
  fin_cases i <;> simp [mulVec,dotProduct,Fin.sum_univ_three,hg.1,hg.2.1,hg.2.2]

omit [CharP F 2] in
/-- The dual quotient by the annihilator plane is central. -/
theorem dual_quotient_fixed (g : pointLocalSL F) (v : Fin 3 → F) :
    (g.val⁻¹.val.transpose *ᵥ v) 0 = v 0 := by
  have hg := (mem_pointLocalSL_iff F g.val⁻¹).mp ((pointLocalSL F).inv_mem g.property)
  simp only [mulVec,dotProduct,Fin.sum_univ_three,transpose_apply]
  rw [hg.1,hg.2.1,hg.2.2]
  simp

omit [CharP F 2] in
/-- The common plane is irreducible among all additive subgroups. -/
theorem natural_irreducible {A : Type*} [Group A] (p : A →* SL(2,F))
    (hp : Function.Surjective p) (W : Subgroup (Multiplicative (Fin 2 → F)))
    (hW : ∀ a w, w ∈ W → Matrix.SL2.naturalAction F (p a) w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  apply Matrix.SL2.naturalAction_irreducible
  intro g w hw
  obtain ⟨a,rfl⟩ := hp g
  exact hW a w hw

variable [Finite F]
theorem pointProjection_ker : (pointProjection F).ker = pCore 2 (pointLocalSL F) :=
  (pointLocalSL_twoCore_eq F).symm

end Representation.SL3PointConstituents
