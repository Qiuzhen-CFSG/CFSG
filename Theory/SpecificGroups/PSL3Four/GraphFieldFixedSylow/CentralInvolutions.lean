module

public import Theory.SpecificGroups.PSL3Four.SylowModel.MatrixRealization
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.ProjectiveFixer.Model
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Central involutions determine Sylow two-subgroups of PSL₃(4)

The centralizer of a nonidentity highest-root element is the projective
upper unitriangular group. A projectively commuting matrix commutes already
in SL: taking traces of the scalar conjugacy equation removes the scalar.
The entry equations then force an upper triangular matrix with equal diagonal
entries, so its projective class is upper unitriangular. Sylow conjugacy
transports this calculation to every Sylow two-subgroup.

This supplies the intrinsic involution-centralizer step for graph-field
fixed-Sylow saturation, used in Aschbacher–Smith, combined manuscript of
1 March 2004, proof of 16.4.9(2), printed p.1191. The argument is a direct
calculation on the genuine PSL₃(4) carrier.
-/

@[expose] public section

open Matrix Subgroup
open Matrix.PSL3Four.SylowModel
open Matrix.PSL3Four.SylowModel.MatrixRealization
open Matrix.PSL3Four.ExtendedCentralizer.ProjectiveFixer
namespace Matrix.PSL3Four.GraphFieldFixedSylow
noncomputable section

private theorem central_lift (A : SL) (c : F)
    (h : Commute (project A) (projective ⟨0, 0, c⟩)) :
    Commute A (specialLinear ⟨0, 0, c⟩) := by
  let Z := specialLinear ⟨0, 0, c⟩
  change Commute (project A) (project Z) at h
  have he : project (A * Z * A⁻¹) = project Z := by
    simpa only [map_mul, map_inv, mul_inv_cancel_right] using
      congrArg (fun x : PSL => x * (project A)⁻¹) h.eq
  obtain ⟨r, _, hr⟩ := (project_eq_iff _ _).mp he
  have ht := congrArg Matrix.trace hr
  have ht' : Matrix.trace ((A * Z * A⁻¹).val) = Matrix.trace Z.val := by
    change Matrix.trace (A.val * Z.val * A⁻¹.val) = _
    rw [Matrix.trace_mul_cycle]
    have hA : A⁻¹.val * A.val = 1 := congrArg Subtype.val (inv_mul_cancel A)
    rw [hA, one_mul]
  rw [ht'] at ht
  change Matrix.trace (matrix ⟨0, 0, c⟩) =
    Matrix.trace (Matrix.scalar (Fin 3) r * matrix ⟨0, 0, c⟩) at ht
  have hr1 : r = 1 := by
    simpa [matrix, Matrix.trace, Matrix.diag,
      Fin.sum_univ_three, Matrix.scalar_apply, Matrix.mul_apply,
      CharTwo.add_self_eq_zero] using ht.symm
  have hz : A * Z * A⁻¹ = Z := by
    apply Subtype.ext
    simpa [hr1] using hr
  change A * Z = Z * A
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using congrArg (· * A) hz

private theorem central_coordinates (A : SL) (c : F) (hc : c ≠ 0)
    (h : Commute A (specialLinear ⟨0, 0, c⟩)) :
    A 1 0 = 0 ∧ A 2 0 = 0 ∧ A 2 1 = 0 ∧ A 0 0 = A 2 2 := by
  have he : A.val * matrix ⟨0, 0, c⟩ = matrix ⟨0, 0, c⟩ * A.val :=
    congrArg Subtype.val h.eq
  have h00 := congrArg (fun B : Matrix (Fin 3) (Fin 3) F => B 0 0) he
  have h01 := congrArg (fun B : Matrix (Fin 3) (Fin 3) F => B 0 1) he
  have h12 := congrArg (fun B : Matrix (Fin 3) (Fin 3) F => B 1 2) he
  have h02 := congrArg (fun B : Matrix (Fin 3) (Fin 3) F => B 0 2) he
  simp [matrix, Matrix.mul_apply, Fin.sum_univ_three] at h00 h01 h12 h02
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h12.resolve_right hc
  · exact h00.resolve_left hc
  · exact h01.resolve_left hc
  · apply mul_right_cancel₀ hc
    exact (add_right_cancel (h02.trans (add_comm _ _))).trans (mul_comm _ _)

private theorem central_mem_range (A : SL) (c : F) (hc : c ≠ 0)
    (h : Commute A (specialLinear ⟨0, 0, c⟩)) :
    project A ∈ projective.range := by
  obtain ⟨h10, h20, h21, h02⟩ := central_coordinates A c hc h
  have hd : A 0 0 * A 1 1 * A 0 0 = 1 := by
    have hh := A.property
    rw [Matrix.det_fin_three] at hh
    simpa [h10, h20, h21, ← h02] using hh
  have ha : A 0 0 ≠ 0 := by intro he; simp [he] at hd
  have h3 : (A 0 0) ^ 3 = 1 := congrArg Units.val (unit_cube (Units.mk0 _ ha))
  have hdiag : A 1 1 = A 0 0 := by
    apply mul_left_cancel₀ ha
    apply mul_right_cancel₀ ha
    exact hd.trans (by simpa [pow_succ] using h3.symm)
  refine ⟨⟨A 0 1 / A 0 0, A 1 2 / A 0 0, A 0 2 / A 0 0⟩, ?_⟩
  symm
  apply (project_eq_iff _ _).mpr
  refine ⟨A 0 0, h3, ?_⟩
  change A.val = Matrix.scalar (Fin 3) (A 0 0) * matrix _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, ← h02, hdiag,
      ha, mul_div_cancel₀]

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The projective image of the standard upper unitriangular matrices. -/
def unipotentSylow : Sylow 2 PSL := Sylow.ofCard projective.range (by
  rw [← Nat.card_congr (MonoidHom.ofInjective projective_injective).toEquiv,
    card_U, card_PSL]
  decide +kernel)

/-- The coordinate group embeds faithfully onto the projective unipotent Sylow. -/
def unipotentEquiv : U ≃* unipotentSylow := MonoidHom.ofInjective projective_injective

/-- A nontrivial highest-root element has precisely the unipotent centralizer. -/
theorem centralizer_highestRoot (c : F) (hc : c ≠ 0) :
    centralizer ({projective ⟨0, 0, c⟩} : Set PSL) = (unipotentSylow : Subgroup PSL) := by
  apply le_antisymm
  · intro x hx
    induction x using QuotientGroup.induction_on with | H A =>
    exact central_mem_range A c hc (central_lift A c
      (mem_centralizer_singleton_iff.mp hx))
  · rintro x ⟨u, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    exact (show Commute u (⟨0, 0, c⟩ : U) from
      (commute_iff _ _).mpr (by simp)).map projective

private theorem unipotent_center_centralizer (z : unipotentSylow)
    (hz : z ∈ center unipotentSylow) (hne : z ≠ 1) :
    centralizer ({(z : PSL)} : Set PSL) = (unipotentSylow : Subgroup PSL) := by
  let u := unipotentEquiv.symm z
  have hu : u ∈ center U := (centerCongr unipotentEquiv.symm ⟨z, hz⟩).property
  obtain ⟨hx, hy⟩ := (mem_center_U _).mp hu
  have he : u = ⟨0, 0, u.c⟩ := U.ext hx hy rfl
  have hzval : (z : PSL) = projective ⟨0, 0, u.c⟩ := by
    have hh := congrArg Subtype.val (unipotentEquiv.apply_symm_apply z)
    change projective u = (z : PSL) at hh
    rw [he] at hh
    exact hh.symm
  have hc : u.c ≠ 0 := by
    intro hc
    apply hne
    apply Subtype.ext
    rw [hzval, hc]
    exact map_one projective
  rw [hzval]
  exact centralizer_highestRoot _ hc

/-- Each nonidentity element in the center of a Sylow two-subgroup of
PSL₃(4) has that Sylow as its full ambient centralizer. -/
theorem centralizer_of_sylow_center (S : Sylow 2 PSL) (z : S)
    (hz : z ∈ center S) (hne : z ≠ 1) :
    centralizer ({(z : PSL)} : Set PSL) = (S : Subgroup PSL) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq PSL unipotentSylow S
  let e := unipotentSylow.equivSMul g
  let z₀ := e.symm z
  have hz₀ : z₀ ∈ center unipotentSylow := (centerCongr e.symm ⟨z, hz⟩).property
  have hn₀ : z₀ ≠ 1 := by
    intro he
    apply hne
    exact e.symm.injective (he.trans (map_one e.symm).symm)
  have hc := unipotent_center_centralizer z₀ hz₀ hn₀
  apply le_antisymm
  · intro x hx
    have hx' : (MulAut.conj g).symm x ∈ (unipotentSylow : Subgroup PSL) := by
      rw [← hc]
      apply mem_centralizer_singleton_iff.mpr
      exact (show Commute x (z : PSL) from mem_centralizer_singleton_iff.mp hx).map
        (MulAut.conj g).symm
    change x ∈ (unipotentSylow : Subgroup PSL).map (MulAut.conj g).toMonoidHom
    exact ⟨_, hx', (MulAut.conj g).apply_symm_apply x⟩
  · intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hz ⟨x, hx⟩))

end
end Matrix.PSL3Four.GraphFieldFixedSylow
