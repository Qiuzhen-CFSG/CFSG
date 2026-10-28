module

public import Theory.SpecificGroups.OmegaSixThree.LocalStructure
public import Theory.SpecificGroups.ClassicalOrthogonal.D3ExteriorComparison.General

/-!
# The concrete ternary six-space commutator group is PSL₄(3)

A hyperbolic basis identifies the displayed diagonal quadratic function with
three hyperbolic planes. Conjugating the full isometry group identifies its
derived subgroup with the elementary split orthogonal group. The already
proved exterior-square surjection from SL₄ has precisely its center as kernel
over the three-element field, so this derived group is PSL₄(3).

This comparison supplies the model identification and simplicity used in the
F.5 uniqueness-system recognition. It uses no group-order computation.
Source: Aschbacher--Smith F.5, printed pp.299--304; GLS3 §2.7.
-/

open Theory.AlgebraicGroup ClassicalOrthogonal
open scoped commutatorElement

noncomputable section
namespace OmegaSixThree
namespace Comparison

abbrev V := VectorD 3 (ZMod 3)
abbrev Q := formD 3 (ZMod 3)
abbrev SL := Matrix.SpecialLinearGroup (Fin 4) (ZMod 3)
abbrev PSL := Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)

def coordinates : V ≃ₗ[ZMod 3] Space where
  toFun v := ![v (.inl 0) - v (.inr 0) + v (.inl 1) - v (.inr 1),
    v (.inl 0) - v (.inr 0) - v (.inl 1) + v (.inr 1),
    v (.inl 0) + v (.inr 0), v (.inl 1) + v (.inr 1),
    v (.inl 2) + v (.inr 2), v (.inl 2) - v (.inr 2)]
  invFun v := Sum.elim ![v 0 + v 1 - v 2, v 0 - v 1 - v 3, -v 4 - v 5]
    ![-v 0 - v 1 - v 2, -v 0 + v 1 - v 3, -v 4 + v 5]
  left_inv v := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp <;> ring_nf <;>
      simp [show (3 : ZMod 3) = 0 by decide, show (2 : ZMod 3) = -1 by decide]
  right_inv v := by
    funext i
    fin_cases i <;> simp <;> ring_nf <;>
      simp [show (4 : ZMod 3) = 1 by decide, show (2 : ZMod 3) = -1 by decide]
  map_add' v w := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> simp <;> ring

theorem quadratic_coordinates (v : V) :
    SixTernaryCoordinates.quadratic (coordinates v) = Q v := by
  simp [SixTernaryCoordinates.quadratic, coordinates, formD_apply, Fin.sum_univ_succ]
  ring_nf
  simp [show (3 : ZMod 3) = 0 by decide, show (4 : ZMod 3) = 1 by decide,
    show (2 : ZMod 3) = -1 by decide]

theorem omega_eq_commutator : omegaPlusSixThree = ⁅orthogonalGroup, orthogonalGroup⁆ := by
  rw [omegaPlusSixThree, Subgroup.commutator_def]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq, commutatorWord, commutatorElement_def]
  aesop

def orthogonalEquiv : quadraticIsometrySubgroup Q ≃* orthogonalGroup where
  toFun g := ⟨coordinates.symm.trans (g.val.trans coordinates), by
    intro v
    change SixTernaryCoordinates.quadratic (coordinates (g.val (coordinates.symm v))) = _
    rw [quadratic_coordinates, (mem_quadraticIsometrySubgroup Q g.val).mp g.prop,
      ← quadratic_coordinates, coordinates.apply_symm_apply]⟩
  invFun g := ⟨coordinates.trans (g.val.trans coordinates.symm), by
    apply (mem_quadraticIsometrySubgroup Q _).mpr
    intro v
    change Q (coordinates.symm (g.val (coordinates v))) = Q v
    rw [← quadratic_coordinates, coordinates.apply_symm_apply, g.prop,
      quadratic_coordinates]⟩
  left_inv g := by
    apply Subtype.ext
    ext v
    simp
  right_inv g := by
    apply Subtype.ext
    ext v
    simp
  map_mul' g h := by
    apply Subtype.ext
    ext v
    simp

def elementaryEquivOmega : elementarySubgroup Q ≃* omegaPlusSixThree :=
  (MulEquiv.subgroupCongr
      (ClassicalOrthogonal.D3ExteriorComparison.General.elementary_eq_commutator
        (F := ZMod 3) (by decide))).trans
    ((orthogonalEquiv.subgroupMap _).trans
      ((MulEquiv.subgroupCongr (by
        rw [_root_.commutator_def, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ orthogonalEquiv.surjective]
        rfl)).trans
        (((commutator orthogonalGroup).equivMapOfInjective orthogonalGroup.subtype
          Subtype.val_injective).trans
          (MulEquiv.subgroupCongr (by
            rw [Subgroup.map_subtype_commutator, omega_eq_commutator])))))

namespace Exterior
open ClassicalOrthogonal.D3ExteriorComparison.General

def lift : SL →* elementarySubgroup Q := toElementary (by decide)

theorem lift_eq_one_iff (g : SL) :
    lift g = 1 ↔ g ∈ Subgroup.center SL := by
  constructor
  · intro h
    apply (toProjective_eq_one_iff_center (by decide) g).mp
    change projectiveElementaryMap Q (lift g) = 1
    rw [h, map_one]
  · intro h
    obtain ⟨a, ha, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
    have ha2 : a ^ 2 = 1 := by
      norm_num only [Fintype.card_fin] at ha
      exact (show ∀ a : ZMod 3, a ^ 4 = 1 → a ^ 2 = 1 by decide) a ha
    apply Subtype.ext
    exact (Kernel.toOrthogonal_eq_one_iff g).mpr ⟨a, ha2, by
      simpa [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal] using he.symm⟩

def projectiveLift : PSL →* elementarySubgroup Q :=
  QuotientGroup.lift _ lift (fun g hg => (lift_eq_one_iff g).mpr hg)

theorem projectiveLift_bijective : Function.Bijective projectiveLift := by
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL) x
    change lift g = 1 at hx
    exact (QuotientGroup.eq_one_iff g).mpr ((lift_eq_one_iff g).mp hx)
  · intro x
    obtain ⟨g, rfl⟩ := toElementary_surjective (F := ZMod 3) (by decide) x
    exact ⟨QuotientGroup.mk g, rfl⟩

def projectiveEquiv : PSL ≃* elementarySubgroup Q :=
  MulEquiv.ofBijective projectiveLift projectiveLift_bijective

end Exterior

end Comparison

/-- The diagonal commutator model used by F.5 is the actual PSL₄(3) carrier. -/
public def omegaEquivPSL :
    omegaPlusSixThree ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3) :=
  Comparison.elementaryEquivOmega.symm.trans Comparison.Exterior.projectiveEquiv.symm

/-- Simplicity of the concrete group acting on the F.5 orthogonality graph. -/
public theorem omega_simple : IsSimpleGroup omegaPlusSixThree := by
  let _ := Atlas.psl_simple_high_rank (F := ZMod 3) 4 (by decide)
  exact omegaEquivPSL.isSimpleGroup

end OmegaSixThree
