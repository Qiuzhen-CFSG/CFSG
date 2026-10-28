module

public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic
public import Theory.SpecificGroups.SL2.Affine.Action
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Two-residuals and root commutators of line stabilizers in SL₂

For a finite field of characteristic two with at least four elements, the
full setwise stabilizer of any field line is two-perfect. Its commutators
with the pointwise line fixer exhaust that fixer. Complete a nonzero line
vector to an SL₂ matrix to conjugate both groups to the standard upper
Borel and root group. A nonidentity diagonal element supplies every root
element as a commutator, using its nontrivial square multiplier.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.3, printed pp.333–334 (PDF pp.344–345). This extends the standard
Borel calculation in `SL2.BorelSmallInvariant.Basic` to an actual field line.
-/

public section

open Subgroup Matrix
open scoped MatrixGroups Pointwise commutatorElement
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F]
local notation "e₀" => (![1, 0] : Fin 2 → F)
local notation "P₀" => (F ∙ e₀)
local notation "u" => transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one

private theorem mem_standardLine (v : Fin 2 → F) : v ∈ P₀ ↔ v 1 = 0 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    simp
  · intro hv
    refine ⟨v 0, ?_⟩
    ext i
    fin_cases i <;> simp [hv]

private theorem standardLine_stabilizer [Finite F] :
    MulAction.stabilizer SL(2,F) (P₀ : Set (Fin 2 → F)) = rankOneBorel F := by
  ext x
  rw [MulAction.mem_stabilizer_set' (Set.toFinite _), mem_rankOneBorel_iff]
  constructor
  · intro hx
    have h := (mem_standardLine _).mp (hx (Submodule.mem_span_singleton_self e₀))
    change (x.val *ᵥ e₀) 1 = 0 at h
    simpa [mulVec, dotProduct, Fin.sum_univ_two] using h
  · intro hx v hv
    apply (mem_standardLine _).mpr
    have hv := (mem_standardLine _).mp hv
    change (x.val *ᵥ v) 1 = 0
    simp [mulVec, dotProduct, Fin.sum_univ_two, hx, hv]

private theorem standardLine_fixer :
    fixingSubgroup SL(2,F) (P₀ : Set (Fin 2 → F)) = upperUnipotent F := by
  ext x
  rw [mem_fixingSubgroup_iff, mem_upperUnipotent]
  constructor
  · intro hx
    have he := hx e₀ (Submodule.mem_span_singleton_self e₀)
    change x.val *ᵥ e₀ = e₀ at he
    have h00 : x.val 0 0 = 1 := by
      simpa [mulVec, dotProduct, Fin.sum_univ_two] using congrFun he 0
    have h10 : x.val 1 0 = 0 := by
      simpa [mulVec, dotProduct, Fin.sum_univ_two] using congrFun he 1
    have h11 : x.val 1 1 = 1 := by
      simpa only [det_fin_two, h00, h10, mul_zero, sub_zero, one_mul] using x.property
    refine ⟨x.val 0 1, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [transvection_coe, h00, h10, h11]
  · rintro ⟨t, rfl⟩ v hv
    have hv := (mem_standardLine _).mp hv
    change (u t).val *ᵥ v = v
    ext i
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, transvection_coe, hv]

private theorem exists_standardLine_smul (P : Submodule F (Fin 2 → F))
    (hP : Module.finrank F P = 1) :
    ∃ a : SL(2,F), a • (P₀ : Set (Fin 2 → F)) = (P : Set (Fin 2 → F)) := by
  have hne : P ≠ ⊥ := (Submodule.isAtom_iff_finrank_eq_one.mpr hP).ne_bot
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨a, ha⟩ := Matrix.SL2.exists_mulVec_eq F e₀ v (by
    intro he
    have := congrFun he 0
    simp at this) hv0
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hP hv hv0]
  refine ⟨a, ?_⟩
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    change c • v = a.val *ᵥ (c • e₀)
    rw [Matrix.mulVec_smul, ha]
  · intro hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    refine ⟨c • e₀, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    change a.val *ᵥ (c • e₀) = c • v
    rw [Matrix.mulVec_smul, ha]

/-- The full setwise stabilizer of a field line has no nontrivial two-group quotient. -/
theorem lineStabilizer_isPPerfect [Finite F] [CharP F 2]
    (P : Submodule F (Fin 2 → F)) (hP : Module.finrank F P = 1)
    (hq : 4 ≤ Nat.card F) : IsPPerfect 2
      (MulAction.stabilizer SL(2,F) (P : Set (Fin 2 → F))) := by
  obtain ⟨a, ha⟩ := exists_standardLine_smul P hP
  let e := MulAction.stabilizerEquivStabilizer ha.symm
  have hstd : IsPPerfect 2 (MulAction.stabilizer SL(2,F) (P₀ : Set (Fin 2 → F))) := by
    rw [standardLine_stabilizer]
    exact rankOneBorel_isPPerfect hq
  exact hstd.of_surjective e.toMonoidHom e.surjective

/-- Diagonal commutators exhaust the standard upper root group. -/
theorem commutator_upperUnipotent_rankOneBorel [Finite F] [CharP F 2]
    (hq : 4 ≤ Nat.card F) : ⁅upperUnipotent F, rankOneBorel F⁆ = upperUnipotent F := by
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp le_rfl)
  rw [commutator_comm]
  have hlarge : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hlarge
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  have ha1 : (a : F) ≠ 1 := by simpa using ha
  have hasq : (a : F) ^ 2 ≠ 1 := by
    intro h
    exact ha1 ((frobenius_inj F 2) (by simpa [frobenius_def] using h))
  intro x hx
  obtain ⟨t, rfl⟩ := (mem_upperUnipotent F x).mp hx
  rw [← commutator_diag2_transvection (a : F) a.ne_zero (t / ((a : F)^2 - 1)) t
    (div_mul_cancel₀ t (sub_ne_zero_of_ne hasq)).symm]
  exact commutator_mem_commutator (diag_mem_rankOneBorel _ _) (by
    exact (mem_upperUnipotent F _).mpr ⟨_, rfl⟩)

/-- The pointwise line fixer is its commutator with the full setwise stabilizer. -/
theorem commutator_lineFixer_stabilizer [Finite F] [CharP F 2]
    (P : Submodule F (Fin 2 → F)) (hP : Module.finrank F P = 1)
    (hq : 4 ≤ Nat.card F) :
    ⁅fixingSubgroup SL(2,F) (P : Set (Fin 2 → F)),
      MulAction.stabilizer SL(2,F) (P : Set (Fin 2 → F))⁆ =
      fixingSubgroup SL(2,F) (P : Set (Fin 2 → F)) := by
  obtain ⟨a, ha⟩ := exists_standardLine_smul P hP
  have hB : MulAction.stabilizer SL(2,F) (P : Set (Fin 2 → F)) =
      (rankOneBorel F).map (MulAut.conj a).toMonoidHom := by
    rw [← ha, MulAction.stabilizer_smul_eq_stabilizer_map_conj, standardLine_stabilizer]
  have hR : fixingSubgroup SL(2,F) (P : Set (Fin 2 → F)) =
      (upperUnipotent F).map (MulAut.conj a).toMonoidHom := by
    rw [← ha, SubMulAction.fixingSubgroup_smul_eq_fixingSubgroup_map_conj, standardLine_fixer]
  rw [hB, hR, ← map_commutator, commutator_upperUnipotent_rankOneBorel hq]
end Matrix.SpecialLinearGroup
