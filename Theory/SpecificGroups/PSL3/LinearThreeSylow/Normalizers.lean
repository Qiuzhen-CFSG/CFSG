module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Mathlib.LinearAlgebra.Matrix.Trace
/-!
# Borel and local Sylow normalizers in degree three

The normalizer of the upper-unitriangular group in SL₃ fixes its common
vector line and covector line, hence is upper triangular. Conversely, upper
triangular conjugation preserves the unitriangular conditions.
In characteristic two, a scalar multiple of a unitriangular matrix has trace
equal to that scalar. Trace invariance under conjugation therefore removes
any scalar ambiguity when lifting the projective normalizer.

Restriction gives Sylow subgroups and their normalizers inside both local
factors. A diagonal element proves that the full Borel strictly contains the
Sylow subgroup when the field has more than two elements.
Source: Aschbacher–Smith, F.1.12(I)(1), printed pp.262–264.
-/

@[expose] public section
open scoped MatrixGroups
open Matrix Matrix.PSL3 Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [Finite F]

theorem borelSL_le_normalizer_unipotentSL :
    borelSL F ≤ Subgroup.normalizer (unipotentSL F) := by
  rw [Subgroup.le_normalizer_iff]
  intro g hg u hu
  obtain ⟨g10,g20,g21⟩ := (mem_borelSL_iff F g).mp hg
  obtain ⟨i10,i20,i21⟩ := (mem_borelSL_iff F g⁻¹).mp ((borelSL F).inv_mem hg)
  have h00 := congrArg (fun a : SL(3,F) => a.val 0 0) (mul_inv_cancel g)
  have h22 := congrArg (fun a : SL(3,F) => a.val 2 2) (mul_inv_cancel g)
  simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
    i10,i20,g20,g21,mul_zero,zero_mul,add_zero,zero_add] at h00 h22
  have hu' := (mem_unipotentSL_iff F u).mp hu
  rw [unipotentSL, Subgroup.mem_inf, mem_pointLocalSL_iff, mem_lineLocalSL_iff]
  simp only [SpecialLinearGroup.coe_mul]
  rw [hu']
  simp [-SpecialLinearGroup.coe_inv, Matrix.mul_apply, Fin.sum_univ_three,
    g10,g20,g21,i10,i20,i21,h00,h22]

theorem normalizer_unipotentSL_le_borelSL :
    Subgroup.normalizer (unipotentSL F) ≤ borelSL F := by
  intro g hg
  have hcol (u : U F) (i : Fin 3) :
      (specialLinear F u * g).val i 0 = g.val i 0 := by
    let v := g⁻¹ * specialLinear F u * g
    have hv : v ∈ unipotentSL F :=
      (Subgroup.mem_normalizer_iff''.mp hg _).mp
        ((specialLinear_range F).le ⟨u,rfl⟩)
    have hv' := (mem_pointLocalSL_iff F v).mp hv.1
    have he : specialLinear F u * g = g * v := by dsimp [v]; group
    rw [he]
    simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
      hv'.1,hv'.2.1,hv'.2.2]
  have hrow (u : U F) (j : Fin 3) :
      (g * specialLinear F u).val 2 j = g.val 2 j := by
    let v := g * specialLinear F u * g⁻¹
    have hv : v ∈ unipotentSL F :=
      (Subgroup.mem_normalizer_iff.mp hg _).mp
        ((specialLinear_range F).le ⟨u,rfl⟩)
    have hv' := (mem_lineLocalSL_iff F v).mp hv.2
    have he : g * specialLinear F u = v * g := by dsimp [v]; group
    rw [he]
    simp [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
      hv'.1,hv'.2.1,hv'.2.2]
  have h10 := hcol ⟨1,0,0⟩ 0
  have h20 := hcol ⟨0,1,0⟩ 1
  have h21 := hrow ⟨0,1,0⟩ 2
  change (matrix F ⟨1,0,0⟩ * g.val) 0 0 = g.val 0 0 at h10
  change (matrix F ⟨0,1,0⟩ * g.val) 1 0 = g.val 1 0 at h20
  change (g.val * matrix F ⟨0,1,0⟩) 2 2 = g.val 2 2 at h21
  simp [matrix, Matrix.mul_apply, Fin.sum_univ_three] at h10 h20 h21
  exact (mem_borelSL_iff F g).mpr ⟨h10,h20,h21⟩

theorem normalizer_unipotentSL : Subgroup.normalizer (unipotentSL F) = borelSL F :=
  le_antisymm (normalizer_unipotentSL_le_borelSL F) (borelSL_le_normalizer_unipotentSL F)

theorem borel_le_normalizer_unipotent : borel F ≤ Subgroup.normalizer (unipotent F) := by
  exact (Subgroup.map_mono (borelSL_le_normalizer_unipotentSL F)).trans
    ((unipotentSL F).le_normalizer_map (projection F))

omit [Finite F] in
private theorem trace_unipotent [CharP F 2] (u : SL(3,F)) (hu : u ∈ unipotentSL F) :
    Matrix.trace u.val = 1 := by
  rw [(mem_unipotentSL_iff F u).mp hu]
  simp [Matrix.trace, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

omit [Finite F] in
private theorem conjugate_mem_of_projective_mem [CharP F 2]
    (g u : SL(3,F)) (hu : u ∈ unipotentSL F)
    (h : projection F (g*u*g⁻¹) ∈ unipotent F) : g*u*g⁻¹ ∈ unipotentSL F := by
  obtain ⟨v,hv,hvproj⟩ := h
  have hc := (projection F).eq_iff.mp hvproj.symm
  rw [projection_ker] at hc
  obtain ⟨r,_,hr⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  have he : (g*u*g⁻¹).val = r • v.val := by
    calc
      (g*u*g⁻¹).val = (v * (v⁻¹ * (g*u*g⁻¹))).val := by simp only [mul_inv_cancel_left]
      _ = v.val * Matrix.scalar (Fin 3) r := by rw [SpecialLinearGroup.coe_mul, ← hr]
      _ = r • v.val := by
        ext i j
        simp [Matrix.scalar, Matrix.mul_diagonal, mul_comm]
  have ht : Matrix.trace (g*u*g⁻¹).val = 1 := by
    change Matrix.trace (g.val*u.val*g⁻¹.val) = 1
    rw [Matrix.trace_mul_cycle]
    have hi : g⁻¹.val * g.val = 1 :=
      congrArg Subtype.val (inv_mul_cancel g)
    rw [hi, one_mul]
    exact trace_unipotent F u hu
  rw [he, Matrix.trace_smul, trace_unipotent F v hv, smul_eq_mul, mul_one] at ht
  have he' : g*u*g⁻¹ = v := Subtype.ext (by simpa [ht] using he)
  rwa [he']

theorem normalizer_unipotent_of_charTwo [CharP F 2] :
    Subgroup.normalizer (unipotent F) = borel F := by
  apply le_antisymm _ (borel_le_normalizer_unipotent F)
  intro x hx
  obtain ⟨g,rfl⟩ := projection_surjective F x
  have hg : g ∈ Subgroup.normalizer (unipotentSL F) := by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      apply conjugate_mem_of_projective_mem F g u hu
      have h := (Subgroup.mem_normalizer_iff.mp hx (projection F u)).mp
        (Subgroup.mem_map_of_mem (projection F) hu)
      simpa only [map_mul, map_inv] using h
    · intro hu
      have hx' : (projection F g)⁻¹ ∈ Subgroup.normalizer (unipotent F : Set PSL(3,F)) :=
        Subgroup.inv_mem _ hx
      have h := (Subgroup.mem_normalizer_iff.mp hx' (projection F (g*u*g⁻¹))).mp
        (Subgroup.mem_map_of_mem (projection F) hu)
      have hc : g⁻¹ * (g*u*g⁻¹) * (g⁻¹)⁻¹ ∈ unipotentSL F := by
        apply conjugate_mem_of_projective_mem F g⁻¹ _ hu
        simpa only [map_mul, map_inv] using h
      simpa [mul_assoc] using hc
  rw [normalizer_unipotentSL F] at hg
  exact Subgroup.mem_map_of_mem (projection F) hg

theorem normalizer_unipotent {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) :
    Subgroup.normalizer (unipotent F) = borel F := by
  let := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hF]
    simp [Nat.pow_mod, Nat.ne_of_gt hn])
  let : CharP F 2 := ringChar.of_eq hc
  exact normalizer_unipotent_of_charTwo F

/-- Restriction of the ambient Sylow to the point local factor. -/
noncomputable def pointLocalSylow {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) :
    Sylow 2 (pointLocal F) :=
  (unipotentSylow F hn hF).subtype (unipotent_le_pointLocal F)

/-- Restriction of the ambient Sylow to the line local factor. -/
noncomputable def lineLocalSylow {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) :
    Sylow 2 (lineLocal F) :=
  (unipotentSylow F hn hF).subtype (unipotent_le_lineLocal F)

@[simp] theorem coe_pointLocalSylow {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) :
    (pointLocalSylow F hn hF : Subgroup (pointLocal F)) =
      (unipotent F).subgroupOf (pointLocal F) := rfl

@[simp] theorem coe_lineLocalSylow {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) :
    (lineLocalSylow F hn hF : Subgroup (lineLocal F)) =
      (unipotent F).subgroupOf (lineLocal F) := rfl

/-- The normalizer is taken inside the local factor. -/
theorem normalizer_pointLocalSylow {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) :
    Subgroup.normalizer (pointLocalSylow F hn hF : Set (pointLocal F)) =
      (borel F).subgroupOf (pointLocal F) := by
  change Subgroup.normalizer ((unipotent F).subgroupOf (pointLocal F) : Set (pointLocal F)) = _
  rw [← Subgroup.subgroupOf_normalizer_eq (unipotent_le_pointLocal F),
    normalizer_unipotent F hn hF]

/-- The normalizer is taken inside the local factor. -/
theorem normalizer_lineLocalSylow {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) :
    Subgroup.normalizer (lineLocalSylow F hn hF : Set (lineLocal F)) =
      (borel F).subgroupOf (lineLocal F) := by
  change Subgroup.normalizer ((unipotent F).subgroupOf (lineLocal F) : Set (lineLocal F)) = _
  rw [← Subgroup.subgroupOf_normalizer_eq (unipotent_le_lineLocal F),
    normalizer_unipotent F hn hF]

theorem map_normalizer_pointLocalSylow {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) :
    (Subgroup.normalizer (pointLocalSylow F hn hF : Set (pointLocal F))).map
      (pointLocal F).subtype = borel F ⊓ pointLocal F := by
  rw [normalizer_pointLocalSylow F hn hF, Subgroup.subgroupOf_map_subtype]

theorem map_normalizer_lineLocalSylow {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) :
    (Subgroup.normalizer (lineLocalSylow F hn hF : Set (lineLocal F))).map
      (lineLocal F).subtype = borel F ⊓ lineLocal F := by
  rw [normalizer_lineLocalSylow F hn hF, Subgroup.subgroupOf_map_subtype]

omit [Finite F] in
/-- A nontrivial diagonal element survives the projective quotient outside S. -/
theorem pointTorus_project_not_mem_unipotent (a : Fˣ) (ha : a ≠ 1) :
    projection F (pointTorus F a) ∉ unipotent F := by
  rintro ⟨u,hu,hup⟩
  have ht : pointTorus F a ∈ lineLocalSL F := by
    rw [mem_lineLocalSL_iff]
    simp [pointTorus]
  have he : (⟨u,hu.2⟩ : lineLocalSL F) = ⟨pointTorus F a,ht⟩ :=
    lineLocal_projection_injective F hup
  have h00 := congrArg (fun x : lineLocalSL F => x.val.val 0 0) he
  have hu00 := ((mem_pointLocalSL_iff F u).mp hu.1).1
  have ha1 : (a : F) = 1 := by simpa [pointTorus, hu00] using h00.symm
  exact ha (Units.ext ha1)

/-- For q > 2 the torus-bearing Borel is strictly larger than S. -/
theorem unipotent_lt_borel (hF : 2 < Nat.card F) : unipotent F < borel F := by
  have hex : ∃ a : Fˣ, a ≠ 1 := by
    by_contra! h
    have : Subsingleton Fˣ := ⟨fun a b => (h a).trans (h b).symm⟩
    have hc := Nat.card_of_subsingleton (1 : Fˣ)
    rw [Nat.card_units] at hc
    omega
  obtain ⟨a,ha⟩ := hex
  refine lt_of_le_of_ne (unipotent_le_borel F) ?_
  intro he
  apply pointTorus_project_not_mem_unipotent F a ha
  rw [he]
  exact Subgroup.mem_map_of_mem (projection F) (pointTorus_mem_borel F a)
end Matrix.PSL3.LinearThree
