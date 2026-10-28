module
public import Theory.SpecificGroups.SL2.OddBorelMarking

/-!
# Reflections normalizing an odd subgroup of a binary split torus

An element of SL₂ in characteristic two which normalizes a nontrivial odd
subgroup of a Sylow normalizer, but lies outside that normalizer, is an
involution. Simultaneous diagonal coordinates reduce the assertion to a
two-by-two matrix: normalization permutes the two distinct eigenspaces,
and leaving the Borel forces their exchange. The determinant makes the
resulting antidiagonal matrix square to one.

This is the rank-one calculation used in the full-Cartan reflection
selection of DGS, *Groups and Graphs* (1985), (14.2), pp.210--211.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem diagonal_normalizer_outside_borel_square
    (C : Subgroup SL(2,F)) (hne : C ≠ ⊥)
    (hdiag : ∀ x : C, ∃ a : Fˣ, (x : SL(2,F)) = diag2 (a:F) a.ne_zero)
    (g : SL(2,F)) (hn : g ∈ normalizer (C : Set SL(2,F)))
    (hout : g ∉ rankOneBorel F) : g*g=1 := by
  obtain ⟨c,hc,hcne⟩ := C.bot_or_exists_ne_one.resolve_left hne
  obtain ⟨a,ha⟩ := hdiag ⟨c,hc⟩
  change c = diag2 (a:F) a.ne_zero at ha
  have ha1 : (a:F) ≠ 1 := by
    intro he
    apply hcne
    rw [ha]
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diag2_coe',he]
  have haInv : (a:F) ≠ (a:F)⁻¹ := by
    intro he
    have hs : (a:F)^2 = 1 := by
      calc (a:F)^2 = (a:F) * (a:F)⁻¹ := by rw [pow_two]; exact congrArg ((a:F) * ·) he
           _ = 1 := mul_inv_cancel₀ a.ne_zero
    rcases sq_eq_one_iff.mp hs with hh | hh
    · exact ha1 hh
    · exact ha1 (by simpa only [CharTwo.neg_eq] using hh)
  have hconj : g*c*g⁻¹ ∈ C := (mem_normalizer_iff.mp hn c).mp hc
  obtain ⟨b,hb⟩ := hdiag ⟨g*c*g⁻¹,hconj⟩
  change g*c*g⁻¹ = diag2 (b:F) b.ne_zero at hb
  have he : g * diag2 (a:F) a.ne_zero = diag2 (b:F) b.ne_zero * g := by
    simpa only [ha] using (mul_inv_eq_iff_eq_mul.mp hb)
  have h10 : g.val 1 0 ≠ 0 := fun hz => hout ((mem_rankOneBorel_iff g).mpr hz)
  have hab : (a:F) = (b:F)⁻¹ := by
    apply mul_left_cancel₀ h10
    simpa [mul_apply,Fin.sum_univ_two,diag2_coe',mul_comm] using
      congrArg (fun x : SL(2,F) => x.val 1 0) he
  have hba : (b:F) = (a:F)⁻¹ := by
    have hh := congrArg (fun x : F => x⁻¹) hab
    simpa only [inv_inv] using hh.symm
  have h00 : g.val 0 0 = 0 := by
    have hh : g.val 0 0 * ((a:F) - (a:F)⁻¹) = 0 := by
      have hh := congrArg (fun x : SL(2,F) => x.val 0 0) he
      simp [mul_apply,Fin.sum_univ_two,diag2_coe'] at hh
      rw [hba] at hh
      linear_combination hh
    exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr haInv)
  have h11 : g.val 1 1 = 0 := by
    have hh : g.val 1 1 * ((a:F)⁻¹ - (a:F)) = 0 := by
      have hh := congrArg (fun x : SL(2,F) => x.val 1 1) he
      simp [mul_apply,Fin.sum_univ_two,diag2_coe',←hab] at hh
      linear_combination hh
    exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr haInv.symm)
  have hprod : g.val 0 1 * g.val 1 0 = 1 := by
    simpa only [det_fin_two,h00,h11,zero_mul,zero_sub,CharTwo.neg_eq] using g.property
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply,Fin.sum_univ_two,h00,h11,hprod,mul_comm]

/-- Every transporter outside the Borel which normalizes a nontrivial odd
subgroup of that Borel is an actual involution in the rank-one quotient. -/
theorem sylow_odd_subgroup_normalizer_square
    (S : Sylow 2 SL(2,F)) (C : Subgroup SL(2,F))
    (hC : C ≤ normalizer (S : Set SL(2,F))) (ho : Odd (Nat.card C))
    (hne : C ≠ ⊥) (g : SL(2,F))
    (hn : g ∈ normalizer (C : Set SL(2,F)))
    (hout : g ∉ normalizer (S : Set SL(2,F))) : g*g=1 := by
  obtain ⟨a,d,hS,hd⟩ := sylow_odd_subgroup_diagonal_coordinates S C hC ho
  let f := MulAut.conj a
  let D := C.map f.toMonoidHom
  have hD : D ≠ ⊥ := by
    intro he
    exact hne ((map_eq_bot_iff_of_injective C f.injective).mp he)
  have hn' : f g ∈ normalizer (D : Set SL(2,F)) :=
    C.le_normalizer_map f.toMonoidHom (mem_map_of_mem f.toMonoidHom hn)
  have hout' : f g ∉ rankOneBorel F := by
    intro hh
    have hh' : f g ∈ normalizer (((S : Subgroup SL(2,F)).map f.toMonoidHom) : Set SL(2,F)) := by
      rw [hS]
      exact hh
    have hm := ((S : Subgroup SL(2,F)).map f.toMonoidHom).le_normalizer_map
      f.symm.toMonoidHom (mem_map_of_mem f.symm.toMonoidHom hh')
    have hm' : g ∈ normalizer (((S : Subgroup SL(2,F)).map f.toMonoidHom).map
        f.symm.toMonoidHom : Set SL(2,F)) := by
      simpa only [MulEquiv.coe_toMonoidHom,f.symm_apply_apply] using hm
    rw [Subgroup.map_map] at hm'
    have hf : f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      exact f.symm_apply_apply x
    rw [hf,Subgroup.map_id] at hm'
    exact hout hm'
  have hsq := diagonal_normalizer_outside_borel_square D hD (fun x => by
    obtain ⟨y,hy,he⟩ := x.property
    exact ⟨d ⟨y,hy⟩,he ▸ hd ⟨y,hy⟩⟩) (f g) hn' hout'
  apply f.injective
  simpa only [map_mul,map_one] using hsq

end Matrix.SpecialLinearGroup
