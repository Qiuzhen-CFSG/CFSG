module
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCores
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Cubic section centralizers of the degree-three local groups

In SL₃ over the field of four elements, an element whose cube is one and
which centralizes a point-local group modulo its two-core is central in SL₃.
The same holds for the line-local group.

Commutators with the two opposite elementary matrices in the lower block
force a scalar lower block and zero entries below the first diagonal entry.
The determinant and the field's multiplicative exponent identify all three
diagonal entries. The cubic relation then kills the two remaining entries.
Flag duality transfers the result to the line-local subgroup.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, 9.3.8,
used in the SL₃(4) tensor exclusion. The local groups and their two-cores
are the literal coordinate groups of `LinearThreeLocalCores`.
-/

@[expose] public noncomputable section
open Matrix Subgroup
open scoped MatrixGroups commutatorElement
namespace Matrix.PSL3.LinearThree
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem point_core_lower_rows (c : SL(3,F)) (hc : c ∈ (pointLocalSL F).pCoreIn 2)
    (i : Fin 3) (hi : i ≠ 0) (j : Fin 3) : c.val i j = if i=j then 1 else 0 := by
  obtain ⟨c,hc,rfl⟩ := hc
  rw [pointLocalSL_twoCore_eq] at hc
  obtain ⟨h00,h10,h20⟩ := (mem_pointLocalSL_iff F c.val).mp c.property
  obtain ⟨h11,h12,h21,h22⟩ := (mem_pointRadicalSL_iff F c).mp hc
  fin_cases i <;> fin_cases j <;> simp_all

private theorem commutator_lower_rows (x u : SL(3,F))
    (hc : ⁅x,u⁆ ∈ (pointLocalSL F).pCoreIn 2)
    (i : Fin 3) (hi : i ≠ 0) (j : Fin 3) :
    (x*u).val i j = (u*x).val i j := by
  have he : x*u = ⁅x,u⁆ * (u*x) := by simp only [commutatorElement_def]; group
  rw [he, SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  simp only [point_core_lower_rows _ hc i hi]
  simp

private theorem point_section_shape (x : SL(3,F))
    (hc : ⁅zpowers x,pointLocalSL F⁆ ≤ (pointLocalSL F).pCoreIn 2) :
    x.val 1 0 = 0 ∧ x.val 2 0 = 0 ∧ x.val 1 2 = 0 ∧ x.val 2 1 = 0 ∧
      x.val 1 1 = x.val 2 2 := by
  let u := SpecialLinearGroup.transvection (by decide : (1:Fin 3) ≠ 2) (1:F)
  let v := SpecialLinearGroup.transvection (by decide : (2:Fin 3) ≠ 1) (1:F)
  have hu : u ∈ pointLocalSL F := by
    rw [mem_pointLocalSL_iff]
    simp [u,SpecialLinearGroup.transvection_coe]
  have hv : v ∈ pointLocalSL F := by
    rw [mem_pointLocalSL_iff]
    simp [v,SpecialLinearGroup.transvection_coe]
  have h1 := commutator_lower_rows x u (hc (commutator_mem_commutator (mem_zpowers x) hu))
    1 (by decide)
  have h2 := commutator_lower_rows x v (hc (commutator_mem_commutator (mem_zpowers x) hv))
    2 (by decide)
  have hu0 := h1 0
  have hu1 := h1 1
  have hu2 := h1 2
  have hv0 := h2 0
  have hv2 := h2 2
  simp [u,v,SpecialLinearGroup.coe_mul,SpecialLinearGroup.transvection_coe,
    Matrix.mul_apply,Fin.sum_univ_three] at hu0 hu1 hu2 hv0 hv2
  exact ⟨hv0,hu0,hv2,hu1,by simpa [hv2] using hu2⟩

/-- A cubic centralizing the point-local section is central in SL₃(4). -/
theorem cubic_point_section_central (hF : Nat.card F = 4) (x : SL(3,F))
    (hc : ⁅zpowers x,pointLocalSL F⁆ ≤ (pointLocalSL F).pCoreIn 2)
    (hx : x^3=1) : x ∈ center SL(3,F) := by
  obtain ⟨h10,h20,h12,h21,hdiag⟩ := point_section_shape x hc
  have hd : x.val 0 0 * x.val 2 2 ^ 2 = 1 := by
    have h := x.property
    change Matrix.det x.val = 1 at h
    simpa only [Matrix.det_fin_three,h10,h20,h12,h21,hdiag,pow_two,
      mul_zero,zero_mul,sub_zero,add_zero,mul_assoc] using h
  have hn : x.val 2 2 ≠ 0 := by intro hz; simp [hz] at hd
  have hpow : x.val 2 2 ^ 3 = 1 := by
    let := Fintype.ofFinite F
    have hcard : Fintype.card F = 4 := by rwa [←Nat.card_eq_fintype_card]
    simpa only [hcard] using FiniteField.pow_card_sub_one_eq_one (x.val 2 2) hn
  have he : x.val 0 0 = x.val 2 2 := by
    apply mul_right_cancel₀ (pow_ne_zero 2 hn)
    rw [hd, ←pow_succ', hpow]
  have h01 : x.val 0 1 = 0 := by
    have h := congrArg (fun y : SL(3,F) => y.val 0 1) hx
    simp [pow_succ, SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_three,
      h10,h20,h12,h21,hdiag,he] at h
    rw [mul_comm (x.val 0 1), CharTwo.add_self_eq_zero, zero_mul, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hn hn)
  have h02 : x.val 0 2 = 0 := by
    have h := congrArg (fun y : SL(3,F) => y.val 0 2) hx
    simp [pow_succ, SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_three,
      h10,h20,h12,h21,hdiag,he] at h
    rw [mul_comm (x.val 0 2), CharTwo.add_self_eq_zero, zero_mul, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hn hn)
  apply SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨x.val 2 2, ?_, ?_⟩
  · simpa using hpow
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar, h10,h20,h12,h21,hdiag,he,h01,h02]

omit [Finite F] [CharP F 2] in
private theorem flagDuality_lineLocalSL :
    (lineLocalSL F).map (flagDuality F).toMonoidHom = pointLocalSL F := by
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact flagDuality_line_mem F ⟨a, ha⟩
  · intro hg
    exact ⟨flagDuality F g, flagDuality_point_mem F ⟨g, hg⟩,
      (flagDuality F).left_inv g⟩

omit [Finite F] [CharP F 2] in
private theorem flagDuality_lineCore_le :
    ((lineLocalSL F).pCoreIn 2).map (flagDuality F).toMonoidHom ≤
      (pointLocalSL F).pCoreIn 2 := by
  rintro g ⟨a, ⟨b, hb, rfl⟩, rfl⟩
  refine ⟨(pointLineLocalEquiv F).symm b, ?_, rfl⟩
  rw [← pCore_map_iso 2 (pointLineLocalEquiv F).symm]
  exact mem_map_of_mem _ hb

/-- A cubic centralizing the line-local section is central in SL₃(4). -/
theorem cubic_line_section_central (hF : Nat.card F = 4) (x : SL(3,F))
    (hc : ⁅zpowers x,lineLocalSL F⁆ ≤ (lineLocalSL F).pCoreIn 2)
    (hx : x^3=1) : x ∈ center SL(3,F) := by
  have hm := map_mono (f := (flagDuality F).toMonoidHom) hc
  rw [map_commutator, MonoidHom.map_zpowers, flagDuality_lineLocalSL] at hm
  have hz := cubic_point_section_central hF (flagDuality F x)
    (hm.trans flagDuality_lineCore_le) (by rw [← map_pow, hx, map_one])
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro y
  apply (flagDuality F).injective
  simpa only [map_mul] using hz (flagDuality F y)

end Matrix.PSL3.LinearThree
