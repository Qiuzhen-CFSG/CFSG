module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointGeometry
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPlaneGeometry

/-!
# Local valencies of the Hermitian four-space flag

The cosets of the full flag stabilizer in each coordinate parabolic have an
explicit transversal: the identity, and an upper root element followed by the
corresponding coordinate reflection. The root parameter belongs to the fixed
field at the point endpoint and the matrix field at the plane endpoint.
Elimination proves exhaustiveness and the lower matrix entry distinguishes
representatives. Consequently the two indices are |F^σ|+1 and |F|+1.

These are the unequal Hermitian quadrangle valencies used in the unitary
specialization of Aschbacher–Smith F.4.5, F.4.13 and F.4.24, printed pp.275,
280 and287. No recognition theorem or group order is assumed.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourGeneration
open UnitaryFourPlaneGeometry
open Subgroup
public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourValence
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "J" => form F σ hσ
local notation "P" => pointParabolicSU F J
local notation "Q" => planeParabolicSU F J
local notation "B" => borelSU F J

private def planeRep (t : Option F) : Q := match t with
  | none => 1
  | some t => ⟨planeShear F σ hσ t * pairSwap F σ hσ,
      (Q).mul_mem (planeShear_mem_borel F σ hσ t).2 (pairSwap_mem_plane F σ hσ)⟩

private theorem planeRep_inv (t : F) :
    ((planeRep F σ hσ (some t))⁻¹ : Q).val =
      pairSwap F σ hσ * planeShear F σ hσ t := by
  change (planeRep F σ hσ (some t)).val⁻¹ = _
  symm
  apply eq_inv_iff_mul_eq_one.mpr
  apply Subtype.ext
  apply Units.ext
  change ((pairSwap F σ hσ).val.val * (planeShear F σ hσ t).val.val) *
    ((planeShear F σ hσ t).val.val * (pairSwap F σ hσ).val.val) = 1
  rw [planeShear_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairSwap, involutionElement, pairSwapMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ, CharTwo.add_self_eq_zero]

private theorem planeRep_eq_iff (s t : Option F) :
    (planeRep F σ hσ s : Q ⧸ (B).subgroupOf Q) = planeRep F σ hσ t ↔ s = t := by
  rw [QuotientGroup.eq]
  change ((planeRep F σ hσ s)⁻¹ * planeRep F σ hσ t).val ∈ B ↔ _
  rw [mem_borel_iff_restriction]
  change ((planeRep F σ hσ s)⁻¹ * planeRep F σ hσ t).val.val.val 1 0 = 0 ↔ _
  cases s with
  | none =>
    cases t with
    | none => simp [planeRep]
    | some t =>
      simp only [planeRep, inv_one, one_mul]
      change ((planeShear F σ hσ t).val.val * (pairSwap F σ hσ).val.val) 1 0 = 0 ↔ _
      rw [planeShear_val]
      simp [pairSwap, involutionElement, pairSwapMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
  | some s =>
    change (((planeRep F σ hσ (some s))⁻¹ : Q).val.val.val *
      (planeRep F σ hσ t).val.val.val) 1 0 = 0 ↔ _
    rw [planeRep_inv]
    cases t with
    | none =>
      change (((pairSwap F σ hσ).val.val * (planeShear F σ hσ s).val.val) * (1 : Matrix (Fin 4) (Fin 4) F)) 1 0 = 0 ↔ _
      rw [planeShear_val]
      simp [pairSwap, involutionElement, pairSwapMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
    | some t =>
      change (((pairSwap F σ hσ).val.val * (planeShear F σ hσ s).val.val) *
        ((planeShear F σ hσ t).val.val * (pairSwap F σ hσ).val.val)) 1 0 = 0 ↔ _
      rw [planeShear_val, planeShear_val]
      simp only [pairSwap, involutionElement, pairSwapMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
      simp [CharTwo.add_eq_zero, eq_comm]

/-- The plane endpoint sees the projective line over the matrix field. -/
theorem plane_index : ((B).subgroupOf Q).index = Nat.card F + 1 := by
  let f : Option F → Q ⧸ (B).subgroupOf Q := fun t => planeRep F σ hσ t
  have hi : Function.Injective f := fun s t h => (planeRep_eq_iff F σ hσ s t).mp h
  have hs : Function.Surjective f := by
    intro x
    induction x using Quotient.inductionOn with
    | h g =>
      by_cases hg : g.val ∈ B
      · refine ⟨none, QuotientGroup.eq.mpr ?_⟩
        change (1⁻¹ * g).val ∈ B
        simpa using hg
      · refine ⟨some (g.val.val.val 0 0 / g.val.val.val 1 0), QuotientGroup.eq.mpr ?_⟩
        change ((planeRep F σ hσ _)⁻¹ : Q).val * g.val ∈ B
        rw [planeRep_inv]
        exact plane_cell F σ hσ g hg
  rw [Subgroup.index_eq_card, ← Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)]
  let := Fintype.ofFinite F
  simp only [Nat.card_eq_fintype_card, Fintype.card_option]

omit [CharP F 2] in
private theorem point_mem_borel (a : SU F J) (ha : a ∈ P) :
    a ∈ B ↔ a.val.val 2 1 = 0 := by
  obtain ⟨h10,h20,h30⟩ := (mem_pointParabolicSU F _ a).mp ha
  have h31 := (point_last_row_zero F σ hσ a ha).1
  change a ∈ P ∧ a ∈ Q ↔ _
  rw [mem_planeParabolicSU]
  simp [ha, h20,h30,h31]

omit [Finite F] [CharP F 2] in
private theorem fixed (t : FixedBy.subfield F σ) : σ t.val = t.val := t.property

private theorem pointRoot_mem_borel (t : FixedBy.subfield F σ) :
    middleRoot F σ hσ t.val (fixed F σ t) ∈ B := by
  constructor
  · change middleRoot F σ hσ t.val (fixed F σ t) ∈ P
    rw [mem_pointParabolicSU, middleRoot_val]
    simp
  · exact middleRoot_mem_plane F σ hσ t.val (fixed F σ t)

private theorem point_cell (a : P) (ha : a.val ∉ B) :
    ∃ t : FixedBy.subfield F σ,
      middleSwap F σ hσ * middleRoot F σ hσ t.val (fixed F σ t) * a.val ∈ B := by
  have h21 : a.val.val.val 2 1 ≠ 0 := by
    rwa [point_mem_borel F σ hσ a.val a.property] at ha
  have h31 := (point_last_row_zero F σ hσ a.val a.property).1
  let t := a.val.val.val 1 1 / a.val.val.val 2 1
  have ht : σ t = t := by
    have hi := column_isotropic F σ hσ a.val 1
    simp only [h31, map_zero, mul_zero, zero_mul, add_zero, zero_add] at hi
    dsimp [t]
    rw [map_div₀]
    have hs21 : σ (a.val.val.val 2 1) ≠ 0 := by simpa using h21
    field_simp [h21, hs21]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hi
  refine ⟨⟨t,ht⟩, ?_⟩
  have hp : middleSwap F σ hσ * middleRoot F σ hσ t ht * a.val ∈ P :=
    (P).mul_mem ((P).mul_mem (middleSwap_mem_point F σ hσ)
      (pointRoot_mem_borel F σ hσ ⟨t,ht⟩).1) a.property
  rw [point_mem_borel F σ hσ _ hp]
  change ((middleSwap F σ hσ).val.val * (middleRoot F σ hσ t ht).val.val *
    a.val.val.val) 2 1 = 0
  rw [middleRoot_val]
  simp [middleSwap, middleSwapMatrix, involutionElement,
    Matrix.mul_apply, Fin.sum_univ_succ, t, div_mul_cancel₀ _ h21,
    CharTwo.add_self_eq_zero]

private def pointRep (t : Option (FixedBy.subfield F σ)) : P := match t with
  | none => 1
  | some t => ⟨middleRoot F σ hσ t.val (fixed F σ t) * middleSwap F σ hσ,
      (P).mul_mem (pointRoot_mem_borel F σ hσ t).1 (middleSwap_mem_point F σ hσ)⟩

private theorem pointRep_inv (t : FixedBy.subfield F σ) :
    ((pointRep F σ hσ (some t))⁻¹ : P).val =
      middleSwap F σ hσ * middleRoot F σ hσ t.val (fixed F σ t) := by
  change (pointRep F σ hσ (some t)).val⁻¹ = _
  symm
  apply eq_inv_iff_mul_eq_one.mpr
  apply Subtype.ext
  apply Units.ext
  change ((middleSwap F σ hσ).val.val * (middleRoot F σ hσ t.val (fixed F σ t)).val.val) *
    ((middleRoot F σ hσ t.val (fixed F σ t)).val.val * (middleSwap F σ hσ).val.val) = 1
  rw [middleRoot_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [middleSwap, involutionElement, middleSwapMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ, CharTwo.add_self_eq_zero]

private theorem pointRep_eq_iff (s t : Option (FixedBy.subfield F σ)) :
    (pointRep F σ hσ s : P ⧸ (B).subgroupOf P) = pointRep F σ hσ t ↔ s = t := by
  rw [QuotientGroup.eq]
  change ((pointRep F σ hσ s)⁻¹ * pointRep F σ hσ t).val ∈ B ↔ _
  rw [point_mem_borel F σ hσ _ (SetLike.coe_mem _)]
  cases s with
  | none =>
    cases t with
    | none => simp [pointRep]
    | some t =>
      simp only [pointRep, inv_one, one_mul]
      change ((middleRoot F σ hσ t.val (fixed F σ t)).val.val * (middleSwap F σ hσ).val.val) 2 1 = 0 ↔ _
      rw [middleRoot_val]
      simp [middleSwap, involutionElement, middleSwapMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
  | some s =>
    change (((pointRep F σ hσ (some s))⁻¹ : P).val.val.val *
      (pointRep F σ hσ t).val.val.val) 2 1 = 0 ↔ _
    rw [pointRep_inv]
    cases t with
    | none =>
      change (((middleSwap F σ hσ).val.val * (middleRoot F σ hσ s.val (fixed F σ s)).val.val) * (1 : Matrix (Fin 4) (Fin 4) F)) 2 1 = 0 ↔ _
      rw [middleRoot_val]
      simp [middleSwap, involutionElement, middleSwapMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
      simp [Matrix.one_apply]
    | some t =>
      change (((middleSwap F σ hσ).val.val * (middleRoot F σ hσ s.val (fixed F σ s)).val.val) *
        ((middleRoot F σ hσ t.val (fixed F σ t)).val.val * (middleSwap F σ hσ).val.val)) 2 1 = 0 ↔ _
      rw [middleRoot_val, middleRoot_val]
      simp [middleSwap, involutionElement, middleSwapMatrix, Matrix.mul_apply,
        Fin.sum_univ_succ, CharTwo.add_eq_zero]
      exact eq_comm

/-- The point endpoint sees the projective line over the fixed field. -/
theorem point_index : ((B).subgroupOf P).index = Nat.card (FixedBy.subfield F σ) + 1 := by
  let f : Option (FixedBy.subfield F σ) → P ⧸ (B).subgroupOf P := fun t => pointRep F σ hσ t
  have hi : Function.Injective f := fun s t h => (pointRep_eq_iff F σ hσ s t).mp h
  have hs : Function.Surjective f := by
    intro x
    induction x using Quotient.inductionOn with
    | h g =>
      by_cases hg : g.val ∈ B
      · refine ⟨none, QuotientGroup.eq.mpr ?_⟩
        change (1⁻¹ * g).val ∈ B
        simpa using hg
      · obtain ⟨t,ht⟩ := point_cell F σ hσ g hg
        refine ⟨some t, QuotientGroup.eq.mpr ?_⟩
        change ((pointRep F σ hσ _)⁻¹ : P).val * g.val ∈ B
        rw [pointRep_inv]
        exact ht
  rw [Subgroup.index_eq_card, ← Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)]
  let := Fintype.ofFinite (FixedBy.subfield F σ)
  simp only [Nat.card_eq_fintype_card, Fintype.card_option]

end Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourValence
