module

public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.FieldTheory.BinaryTorusTwoPower

/-!
# Residual parameter rigidity for the degree-three split torus

The first axis of the diagonal torus is faithful even in PSL₃: intersecting
that axis with the cubic scalar kernel gives the identity. A graph-field
actor fixing an axis element forces its cube to be one. Binary torus
arithmetic supplies a noncubic element of O³(Fˣ) outside degree two.
For pure field actors, the arbitrary two-power calculation excludes every
nonidentity coefficient automorphism outside degrees two and six.

All projective equalities retain the kernel {(a,a) | a³=1}. The displacement
criterion uses the actual unipotent/torus complement in the Borel. These
parameter calculations do not assert that a general actor preserves a chosen
torus; its action on the Borel quotient must be computed separately.
Source: Aschbacher–Smith, proof of 13.8.20, printed p.954.
-/

public section

open Subgroup
open scoped MatrixGroups
open Matrix.PSL3.CartanActions Matrix.PSL3.CartanActions.BorelQuotient
namespace Matrix.PSL3.CartanActions.ResidualParameters
variable {F : Type*} [Field F]

/-- The projective parameter equality retains the cubic scalar ambiguity. -/
theorem projective_parameters_eq_iff (d e : Fˣ × Fˣ) :
    torusMap F d = torusMap F e ↔
      (d * e⁻¹).1 = (d * e⁻¹).2 ∧ (d * e⁻¹).1 ^ 3 = 1 := by
  rw [← torusMap_eq_one_iff, map_mul, map_inv, mul_inv_eq_one]

/-- The first coordinate axis survives the cubic scalar quotient injectively. -/
theorem projective_axis_injective : Function.Injective (fun u : Fˣ => torusMap F (u,1)) := by
  intro u v huv
  have h := (projective_parameters_eq_iff (u,1) (v,1)).mp huv
  exact mul_inv_eq_one.mp (by simpa using h.1)

/-- A field action on either coordinate cannot hide in the scalar kernel. -/
theorem field_eq_of_projective_axis (σ : F ≃+* F) (u : Fˣ)
    (h : torusMap F (Units.map σ.toMonoidHom u, 1) = torusMap F (u,1)) :
    Units.map σ.toMonoidHom u = u := projective_axis_injective h

/-- A graph-field fixer on an axis forces that axis element to be cubic. -/
theorem cube_eq_one_of_graph_field_axis (σ : F ≃+* F) (u : Fˣ)
    (h : torusMap F (1, (Units.map σ.toMonoidHom u)⁻¹) = torusMap F (u,1)) :
    u ^ 3 = 1 := by
  have h := (projective_parameters_eq_iff _ _).mp h
  simpa only [Prod.fst_mul, Prod.fst_inv, one_mul, inv_pow, inv_eq_one] using h.2

/-- Coefficient actions are faithful already on the first torus axis. -/
theorem fieldAction_injective : Function.Injective (OuterSolvable.fieldAction F) := by
  intro σ τ h
  ext x
  by_cases hx : x = 0
  · simp [hx]
  · let u : Fˣ := Units.mk0 x hx
    have he := congrArg (fun α : MulAut PSL(3,F) => α (torusMap F (u,1))) h
    simp only [field_torusMap, map_one] at he
    exact congrArg Units.val (projective_axis_injective he)

variable [Finite F]

/-- Diagonal displacements in the projective unipotent radical are trivial. -/
theorem torus_displacement_mem_unipotent_iff {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (d e : Fˣ × Fˣ) :
    torusMap F d * (torusMap F e)⁻¹ ∈ LinearThree.unipotent F ↔
      torusMap F d = torusMap F e := by
  constructor
  · intro h
    let x : LinearThree.borel F :=
      ⟨_, LinearThree.unipotent_le_borel F h⟩
    have hx : x = 1 := (Subgroup.disjoint_def.mp (borel_complement F hF).disjoint)
      h ((torus F).mul_mem ⟨d,rfl⟩ ((torus F).inv_mem ⟨e,rfl⟩))
    exact mul_inv_eq_one.mp (congrArg Subtype.val hx)
  · intro h
    rw [h, mul_inv_cancel]
    exact (LinearThree.unipotent F).one_mem

/-- Outside degree two the three-residual of the unit group has a noncubic element. -/
theorem exists_residual_noncubic {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 1 < n) (hn2 : n ≠ 2) :
    ∃ u ∈ pResidual 3 Fˣ, u ^ 3 ≠ 1 := by
  have hp : ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ 2 ^ n - 1 := by
    by_cases hn3 : n = 3
    · subst n
      exact ⟨7, by decide, by decide, by decide⟩
    · exact Nat.BinarySignedTorus.exists_prime_gt_three_dvd_sub (by omega)
  obtain ⟨p,hp,hp3,hd⟩ := hp
  let : Fact p.Prime := ⟨hp⟩
  have hd' : p ∣ Nat.card Fˣ := by rwa [Nat.card_units, hF]
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' p hd'
  refine ⟨u, mem_pResidual_of_orderOf_coprime ?_, ?_⟩
  · rw [hu]
    exact (hp.coprime_iff_not_dvd.mpr (by
      intro h
      have := Nat.le_of_dvd (by decide : 0 < 3) h
      omega)).symm
  · intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hu] at hd
    have := Nat.le_of_dvd (by decide : 0 < 3) hd
    omega

/-- No field twist of the Borel-preserving graph fixes the residual axes,
even after quotienting by the cubic scalars. -/
theorem graph_field_not_fixed {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 1 < n) (hn2 : n ≠ 2) (σ : F ≃+* F) :
    ¬ (∀ u ∈ pResidual 3 Fˣ,
      torusMap F (1, (Units.map σ.toMonoidHom u)⁻¹) = torusMap F (u,1)) := by
  intro h
  obtain ⟨u,hu,huc⟩ := exists_residual_noncubic hF hn hn2
  exact huc (cube_eq_one_of_graph_field_axis σ u (h u hu))

/-- Arbitrary two-power field actors are detected on residual axes. -/
theorem field_eq_one_of_fixed_axes [CharP F 2] {n k : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn2 : n ≠ 2) (hn6 : n ≠ 6)
    (σ : F ≃+* F) (hσ : σ ^ (2 ^ k) = 1)
    (hfix : ∀ u ∈ pResidual 3 Fˣ,
      torusMap F (Units.map σ.toMonoidHom u,1) = torusMap F (u,1)) : σ = 1 :=
  FiniteField.BinaryTorusTwoPower.eq_one_of_fixed_residual hF hn2 hn6 σ hσ
    (fun u hu => field_eq_of_projective_axis σ u (hfix u hu))

end Matrix.PSL3.CartanActions.ResidualParameters
