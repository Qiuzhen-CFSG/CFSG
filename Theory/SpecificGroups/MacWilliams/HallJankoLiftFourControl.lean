module

public import Theory.SpecificGroups.MacWilliams.HallJankoFrameCommonCentralizer
public import Theory.ElementaryAbelian.Join
import Mathlib.Tactic.Group

/-!
# Control of the marked four in a Hall–Janko frame

The common-centralizer bound forces the marked four `W` into the elementary
sixteen `B`. The `tu` defect cannot lie in `W`: otherwise the elementary join
`W ⊔ zpowers u` is normal. Indeed, the base actions normalize this join, `v`
commutes with `u`, and the defect controls conjugation by `t`. These elements
generate the ambient group. The action of `u` on the base is nontrivial, so the
join strictly contains `W` and has order at least eight, a contradiction.

The argument uses only the frame and the local subgroup hypotheses; it does not
require existence or enumeration of extension parameters.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3(a), printed p.386,
citing MacWilliams, Trans. AMS 150 (1970), DOI 10.1090/S0002-9947-1970-0276324-3.
-/

open Subgroup
namespace MacWilliamsSylow.HallJankoActionFrame
variable {P : Type*} [Group P] {D W B : Subgroup P}

private theorem u_not_mem_base [IsMulCommutative D]
    (f : HallJankoActionFrame D W B) (hW : Nat.card W = 4) : f.u ∉ D := by
  intro hu
  have ha : f.a ∈ D := by simp only [f.base]; exact subset_closure (by simp)
  have hb : f.b ∈ D := by simp only [f.base]; exact subset_closure (by simp)
  have ha' : f.a⁻¹ * f.b ^ 2 = f.a := by
    apply mul_right_cancel (b := f.u)
    exact f.ua.symm.trans (D.le_centralizer ha f.u hu)
  have hb' : f.b⁻¹ = f.b := by
    apply mul_right_cancel (b := f.u)
    exact f.ub.symm.trans (D.le_centralizer hb f.u hu)
  have hb2 : f.b ^ 2 = 1 := by simpa only [hb', ← pow_two] using inv_mul_cancel f.b
  have ha2 : f.a ^ 2 = 1 := by
    rw [hb2, mul_one] at ha'
    simpa only [ha', ← pow_two] using inv_mul_cancel f.a
  have hbot : W = ⊥ := by rw [f.four, ha2, hb2]; simp
  rw [hbot, Subgroup.card_bot] at hW
  norm_num at hW

private theorem mem_normalizer_join_of_conj_mem [Finite P] [W.Normal]
    (u g : P) (hg : g * u * g⁻¹ ∈ W ⊔ zpowers u) :
    g ∈ normalizer ((W ⊔ zpowers u : Subgroup P) : Set P) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rw [Subgroup.map_sup, Subgroup.Normal.map_conj_eq W g, MonoidHom.map_zpowers]
    exact sup_le le_sup_left (zpowers_le.mpr hg)
  · rw [card_map_of_injective (MulAut.conj g).injective]

/-- A defect in the marked four would produce a forbidden normal elementary eight. -/
public theorem tu_defect_not_mem_four [Finite P] [W.Normal] [IsElementaryAbelian 2 W]
    [IsMulCommutative D] [IsElementaryAbelian 2 B]
    (f : HallJankoActionFrame D W B)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hW : Nat.card W = 4) (hWD : W ≤ D) (hWB : W ≤ B) :
    f.t * f.u * (f.u * f.t)⁻¹ ∉ W := by
  intro hdef
  let E : Subgroup P := W ⊔ zpowers f.u
  have hWE : W ≤ E := le_sup_left
  have huE : f.u ∈ E := (le_sup_right : zpowers f.u ≤ E) (mem_zpowers f.u)
  have ha2 : f.a ^ 2 ∈ W := by simp only [f.four]; exact subset_closure (by simp)
  have hb2 : f.b ^ 2 ∈ W := by simp only [f.four]; exact subset_closure (by simp)
  have huW : f.u ∉ W := fun h => f.u_not_mem_base hW (hWD h)
  let : IsElementaryAbelian 2 (zpowers f.u) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (by simpa only [pow_two] using f.u_two)
  have hcentral : zpowers f.u ≤ centralizer (W : Set P) := by
    apply zpowers_le.mpr
    intro w hw
    exact congrArg (fun z : B => (z : P))
      (IsMulCommutative.is_comm.comm (⟨w, hWB hw⟩ : B) ⟨f.u, f.u_mem⟩)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.sup_of_le_centralizer hcentral
  have hnorm : E.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← f.generate]
    apply (closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · apply inv_mem_iff.mp
      apply mem_normalizer_join_of_conj_mem
      have he : f.a⁻¹ * f.u * (f.a⁻¹)⁻¹ = (f.a ^ 2)⁻¹ * f.b ^ 2 * f.u := by
        simp only [inv_inv, mul_assoc, f.ua]
        group
      rw [he]
      exact E.mul_mem (hWE (W.mul_mem (W.inv_mem ha2) hb2)) huE
    · apply inv_mem_iff.mp
      apply mem_normalizer_join_of_conj_mem
      have he : f.b⁻¹ * f.u * (f.b⁻¹)⁻¹ = (f.b ^ 2)⁻¹ * f.u := by
        simp only [inv_inv, mul_assoc, f.ub]
        group
      rw [he]
      exact E.mul_mem (hWE (W.inv_mem hb2)) huE
    · exact E.le_normalizer huE
    · apply mem_normalizer_join_of_conj_mem
      simpa only [f.vu, mul_inv_cancel_right] using huE
    · apply mem_normalizer_join_of_conj_mem
      have he : f.t * f.u * f.t⁻¹ = (f.t * f.u * (f.u * f.t)⁻¹) * f.u := by group
      rw [he]
      exact E.mul_mem (hWE hdef) huE
  have hgt : 4 < Nat.card E := by
    by_contra h
    have he : W = E := eq_of_le_of_card_ge hWE (by omega)
    exact huW (he.ge huE)
  have hdvd : 4 ∣ Nat.card E := hW ▸ card_dvd_of_le hWE
  obtain ⟨n, hn⟩ := hdvd
  exact hno ⟨E, hnorm, inferInstance, by omega⟩

/-- Structural control of the marked four, before normalizing the three lifts. -/
public theorem four_le_and_tu_defect_not_mem
    [Finite P] [W.Normal] [IsElementaryAbelian 2 W]
    [D.Normal] [IsMulCommutative D] [IsElementaryAbelian 2 B]
    (f : HallJankoActionFrame D W B) (hcard : Nat.card P = 128)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hW : Nat.card W = 4) (hB : Nat.card B = 16)
    (hWD : W ≤ D) (hDC : centralizer (D : Set P) ≤ D)
    (hDO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))) :
    W ≤ B ∧ f.t * f.u * (f.u * f.t)⁻¹ ∉ W := by
  have hWB := f.four_le_elementary_sixteen_of_c4_square hcard hmodel hDC hDO hW hB
  exact ⟨hWB, f.tu_defect_not_mem_four hno hW hWD hWB⟩

end MacWilliamsSylow.HallJankoActionFrame
