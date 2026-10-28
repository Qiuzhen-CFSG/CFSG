module

public import Theory.SpecificGroups.PSL3Four.SylowModel
public import CFSG.Quasithin.Chapter5.Section03ExceptionalSylowModel.SubgroupGeometry

/-!
# Normal subgroups outside the unipotent group

A subgroup whose image modulo the central involution has exponent two has
Frobenius-fixed root coordinates on every element outside S. Multiplication
by one such element gives the same conclusion for its elements inside S.
Thus the subgroup is contained in the trace kernel Q.

Conversely, normality and an element outside S give both prime-field root
directions through conjugation. Containment of Z supplies every central
coordinate. These directions, Z, and the outside element generate Q.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, §5.3.7,
printed pp. 660--661 (PDF pp. 677--678).
-/

@[expose] public section
noncomputable section
open Matrix.PSL3Four
namespace Matrix.PSL3Four.SylowModel

private theorem outside_mem_Q (W : Subgroup T)
    [IsElementaryAbelian 2 (W.map quotient)] (a : T) (ha : a ∈ W)
    (hr : a.right = τ) : a ∈ Q := by
  have hp : quotient (a ^ 2) = 1 := by
    rw [map_pow]
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := W.map quotient) _ ⟨a, ha, rfl⟩
  have hz := (mem_Z _).mp (C_le_Z ((QuotientGroup.eq_one_iff _).mp hp))
  apply (mem_Q a).mpr
  have hx : trace a.left.x = 0 := by
    simpa only [trace, pow_two, SemidirectProduct.mul_left, hr, action_τ, mul_x, frob_x]
      using hz.2.1
  have hy : trace a.left.y = 0 := by
    simpa only [trace, pow_two, SemidirectProduct.mul_left, hr, action_τ, mul_y, frob_y]
      using hz.2.2
  exact ⟨(trace_eq_zero _).mp hx, (trace_eq_zero _).mp hy⟩

private theorem outside_le_Q (W : Subgroup T)
    [IsElementaryAbelian 2 (W.map quotient)] (hS : ¬ W ≤ S) : W ≤ Q := by
  obtain ⟨a, ha, has⟩ := Set.not_subset.mp hS
  have hr : a.right = τ := (c2_cases _).resolve_left (by simpa using has)
  have haQ := outside_mem_Q W a ha hr
  intro b hb
  rcases c2_cases b.right with hbr | hbr
  · have habQ := outside_mem_Q W (a * b) (W.mul_mem ha hb) (by simp [hr, hbr])
    exact (Q.mul_mem_cancel_left haQ).mp habQ
  · exact outside_mem_Q W b hb hbr

private theorem fixed_cases (x : F) (hx : fieldFrobenius x = x) : x = 0 ∨ x = 1 := by
  have h : x * (x - 1) = 0 := by
    calc
      x * (x - 1) = x ^ 2 - x := by ring
      _ = 0 := sub_eq_zero.mpr hx
  simpa only [sub_eq_zero] using mul_eq_zero.mp h

private theorem exists_trace_one : ∃ t : F, trace t = 1 := by
  obtain ⟨t, ht⟩ := exists_fieldFrobenius_ne
  refine ⟨t, ?_⟩
  apply (fixed_cases (trace t) ?_).resolve_left
  · exact fun h => ht ((trace_eq_zero t).mp h)
  · simp only [trace, map_add, fieldFrobenius_involutive, add_comm]


private theorem mem_of_same_coordinates (W : Subgroup T) (hZ : Z ≤ W)
    {a b : T} (hb : b ∈ W) (hr : a.right = b.right)
    (hx : a.left.x = b.left.x) (hy : a.left.y = b.left.y) : a ∈ W := by
  let d := a * b⁻¹
  have hdr : d.right = 1 := by simp [d, hr]
  have he : d * b = a := by simp [d]
  have hdx : d.left.x = 0 := by
    have h := congrArg (fun t : T => t.left.x) he
    simpa [SemidirectProduct.mul_left, hdr, hx] using h
  have hdy : d.left.y = 0 := by
    have h := congrArg (fun t : T => t.left.y) he
    simpa [SemidirectProduct.mul_left, hdr, hy] using h
  rw [← he]
  exact W.mul_mem (hZ ((mem_Z d).mpr ⟨hdr, hdx, hdy⟩)) hb

private theorem normal_root_coordinates (W : Subgroup T) (hn : W.Normal)
    (a : T) (ha : a ∈ W) (hr : a.right = τ) (u : U) :
    ∃ d ∈ W, d.right = 1 ∧ d.left.x = trace u.x ∧ d.left.y = trace u.y := by
  let g := inclusion u
  let d := g * a * g⁻¹ * a⁻¹
  have hd : d ∈ W := W.mul_mem (hn.conj_mem a ha g) (W.inv_mem ha)
  have hdr : d.right = 1 := by simp [d, g, inclusion]
  have he : d * (a * g) = g * a := by simp [d, mul_assoc]
  refine ⟨d, hd, hdr, ?_, ?_⟩
  · have h := congrArg (fun t : T => t.left.x) he
    simp only [SemidirectProduct.mul_left, hdr, map_one, MulAut.one_apply,
      mul_x, hr, action_τ, frob_x] at h
    change d.left.x + (a.left.x + fieldFrobenius u.x) = u.x + a.left.x at h
    have := congrArg (· + (a.left.x + fieldFrobenius u.x)) h
    simpa [trace, add_assoc, add_comm, add_left_comm, CharTwo.add_self_eq_zero, CharTwo.add_cancel_left] using this
  · have h := congrArg (fun t : T => t.left.y) he
    simp only [SemidirectProduct.mul_left, hdr, map_one, MulAut.one_apply,
      mul_y, hr, action_τ, frob_y] at h
    change d.left.y + (a.left.y + fieldFrobenius u.y) = u.y + a.left.y at h
    have := congrArg (· + (a.left.y + fieldFrobenius u.y)) h
    simpa [trace, add_assoc, add_comm, add_left_comm, CharTwo.add_self_eq_zero, CharTwo.add_cancel_left] using this

private theorem Q_le_normal_outside (W : Subgroup T) (hn : W.Normal)
    (hZ : Z ≤ W) (a : T) (ha : a ∈ W) (haQ : a ∈ Q) (hr : a.right = τ) :
    Q ≤ W := by
  obtain ⟨t, ht⟩ := exists_trace_one
  obtain ⟨d₁, hd₁, hr₁, hx₁, hy₁⟩ := normal_root_coordinates W hn a ha hr ⟨t, 0, 0⟩
  obtain ⟨d₂, hd₂, hr₂, hx₂, hy₂⟩ := normal_root_coordinates W hn a ha hr ⟨0, t, 0⟩
  have hx₁ : d₁.left.x = 1 := hx₁.trans ht
  have hy₁ : d₁.left.y = 0 := hy₁.trans trace_zero
  have hx₂ : d₂.left.x = 0 := hx₂.trans trace_zero
  have hy₂ : d₂.left.y = 1 := hy₂.trans ht
  have hlinear (b : T) (hb : b ∈ Q) (hbr : b.right = 1) : b ∈ W := by
    obtain ⟨hx, hy⟩ := (mem_Q b).mp hb
    rcases fixed_cases _ hx with hx | hx <;> rcases fixed_cases _ hy with hy | hy
    · exact hZ ((mem_Z b).mpr ⟨hbr, hx, hy⟩)
    · exact mem_of_same_coordinates W hZ hd₂ (hbr.trans hr₂.symm)
        (hx.trans hx₂.symm) (hy.trans hy₂.symm)
    · exact mem_of_same_coordinates W hZ hd₁ (hbr.trans hr₁.symm)
        (hx.trans hx₁.symm) (hy.trans hy₁.symm)
    · apply mem_of_same_coordinates W hZ (W.mul_mem hd₁ hd₂)
      · simp [hbr, hr₁, hr₂]
      · simp [SemidirectProduct.mul_left, hr₁, hx₁, hx₂, hx]
      · simp [SemidirectProduct.mul_left, hr₁, hy₁, hy₂, hy]
  intro b hb
  rcases c2_cases b.right with hbr | hbr
  · exact hlinear b hb hbr
  · have hd := hlinear (b * a⁻¹) (Q.mul_mem hb (Q.inv_mem haQ)) (by simp [hbr, hr])
    simpa only [inv_mul_cancel_right] using W.mul_mem hd ha

/-- A normal subgroup containing the unipotent center, with elementary image
modulo the central involution, is the trace kernel if it is not contained in S. -/
theorem normal_outside_eq_Q (W : Subgroup T) (hn : W.Normal) (hZ : Z ≤ W)
    (helem : IsElementaryAbelian 2 (W.map quotient))
    (_hnoncomm : ¬ IsMulCommutative W) (hS : ¬ W ≤ S) : W = Q := by
  let := helem
  have hWQ := outside_le_Q W hS
  obtain ⟨a, ha, has⟩ := Set.not_subset.mp hS
  have hr : a.right = τ := (c2_cases _).resolve_left (by simpa using has)
  exact le_antisymm hWQ (Q_le_normal_outside W hn hZ a ha (hWQ ha) hr)

end Matrix.PSL3Four.SylowModel
