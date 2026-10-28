module
public import Theory.SpecificGroups.PSL3.LinearThreeAdditiveRadical

/-!
# Odd additive actors on the SL₃ point section

An additive automorphism centralizing the point residual modulo its root
plane has scalar action on the last two coordinates. If its odd order is
coprime to q−1, that scalar is one. Elementary transvections then make the
first row field-linear; the same coprimality removes its diagonal scalar.
The remaining shear is an involution, so odd order makes the actor trivial.
No semilinearity, automorphism coverage or splitting is assumed.

The local transvection lemmas adapt the private calculations in
Theory.SpecificGroups.PSL3.LinearThreeAdditiveRadical. The literal original
flag application and Hall contradiction are in the parent LinearAction
module. Source: Aschbacher--Smith, 11.4.4, printed p.778 of
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.LinearAction
open Matrix.PSL3.LinearThree
variable {F : Type*} [Field F]

private def shear (a b : F) (v : Fin 3 → F) : Fin 3 → F :=
  ![v 0 + a * v 1 + b * v 2, v 1, v 2]

private theorem transvection_action {i j : Fin 3} (hij : i ≠ j) (t : F) (v : Fin 3 → F) :
    (SpecialLinearGroup.transvection hij t).val.mulVec v = v + Pi.single i (t * v j) := by
  ext k
  simp [SpecialLinearGroup.transvection_coe, mulVec, dotProduct, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [Matrix.one_apply, add_comm] <;> try ac_rfl

private theorem coordinate_decomposition (f : (Fin 3 → F) →+ (Fin 3 → F)) (v : Fin 3 → F) :
    f v = f (Pi.single 0 (v 0)) + f (Pi.single 1 (v 1)) + f (Pi.single 2 (v 2)) := by
  rw [←map_add,←map_add]
  congr 1
  ext i
  fin_cases i <;> simp

private theorem quotient_scalar (f : (Fin 3 → F) →+ (Fin 3 → F))
    (h : ∀ (i j : Fin 3), i ≠ j → j ≠ 0 → ∀ (t : F), ∃ a b : F, ∀ (v : Fin 3 → F), f (v + Pi.single i (t * v j)) =
        shear a b (f v + Pi.single i (t * f v j))) :
    ∃ c : F, ∀ v, f v 1 = c * v 1 ∧ f v 2 = c * v 2 := by
  have hb (i j : Fin 3) (hij : i ≠ j) (hj : j ≠ 0) (t : F)
      (k : Fin 3) (hk : k = 1 ∨ k = 2) :
      f (Pi.single i t) k = if k = i then t * f (Pi.single j 1) j else 0 := by
    obtain ⟨a,b,he⟩ := h i j hij hj t
    have hh := congrFun (he (Pi.single j 1)) k
    rcases hk with rfl | rfl <;>
      simpa [shear,map_add,Pi.add_apply,Pi.single_apply,add_right_inj] using hh
  have h01 (t : F) : f (Pi.single 0 t) 1 = 0 := by
    simpa using hb 0 1 (by decide) (by decide) t 1 (Or.inl rfl)
  have h02 (t : F) : f (Pi.single 0 t) 2 = 0 := by
    simpa using hb 0 1 (by decide) (by decide) t 2 (Or.inr rfl)
  have h12 (t : F) : f (Pi.single 1 t) 2 = 0 := by
    simpa using hb 1 2 (by decide) (by decide) t 2 (Or.inr rfl)
  have h21 (t : F) : f (Pi.single 2 t) 1 = 0 := by
    simpa using hb 2 1 (by decide) (by decide) t 1 (Or.inl rfl)
  have h11 (t : F) : f (Pi.single 1 t) 1 = t * f (Pi.single 2 1) 2 := by
    simpa using hb 1 2 (by decide) (by decide) t 1 (Or.inl rfl)
  have h22 (t : F) : f (Pi.single 2 t) 2 = t * f (Pi.single 2 1) 2 := by
    simpa [h11] using hb 2 1 (by decide) (by decide) t 2 (Or.inr rfl)
  refine ⟨f (Pi.single 2 1) 2, fun v => ?_⟩
  rw [coordinate_decomposition f v]
  simp only [Pi.add_apply]
  constructor
  · rw [h01 (v 0),h11 (v 1),h21 (v 2)]
    simp only [zero_add,add_zero,mul_comm]
  · rw [h02 (v 0),h12 (v 1),h22 (v 2)]
    simp only [zero_add,add_zero,mul_comm]

private theorem first_row_linear (f : (Fin 3 → F) →+ (Fin 3 → F))
    (h : ∀ (i j : Fin 3), i ≠ j → j ≠ 0 → ∀ (t : F), ∃ a b : F, ∀ (v : Fin 3 → F), f (v + Pi.single i (t * v j)) =
        shear a b (f v + Pi.single i (t * f v j)))
    (hb : ∀ v, f v 1 = v 1 ∧ f v 2 = v 2) :
    ∃ a b c : F, ∀ v, f v = ![a * v 0 + b * v 1 + c * v 2, v 1, v 2] := by
  obtain ⟨a₀,b₀,h₀⟩ := h 0 1 (by decide) (by decide) 1
  obtain ⟨a₁,b₁,h₁⟩ := h 1 2 (by decide) (by decide) 1
  obtain ⟨a₂,b₂,h₂⟩ := h 2 1 (by decide) (by decide) 1
  have ha (z : F) : f (Pi.single 0 z) 0 = (1+a₀) * z := by
    have hh := congrFun (h₀ (Pi.single 1 z)) 0
    simp [shear,map_add,Pi.add_apply,(hb _).1,(hb _).2] at hh
    linear_combination hh
  have hb' (z : F) : f (Pi.single 1 z) 0 = (a₁+b₁) * z := by
    have hh := congrFun (h₁ (Pi.single 2 z)) 0
    simp [shear,map_add,Pi.add_apply,(hb _).1,(hb _).2] at hh
    linear_combination hh
  have hc (z : F) : f (Pi.single 2 z) 0 = (a₂+b₂) * z := by
    have hh := congrFun (h₂ (Pi.single 1 z)) 0
    simp [shear,map_add,Pi.add_apply,(hb _).1,(hb _).2] at hh
    linear_combination hh
  let a := 1+a₀
  let b := a₁+b₁
  let c := a₂+b₂
  refine ⟨a,b,c,fun v => ?_⟩
  ext i
  fin_cases i
  · rw [coordinate_decomposition f v]
    simp [ha,hb',hc,a,b,c]
  · simpa using (hb v).1
  · simpa using (hb v).2

private theorem pow_coordinate (b : MulAut (Multiplicative (Fin 3 → F)))
    (i : Fin 3) (a : F) (h : ∀ v, (b v).toAdd i = a * v.toAdd i)
    (r : ℕ) (v : Multiplicative (Fin 3 → F)) :
    ((b^r) v).toAdd i = a^r * v.toAdd i := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ',MulAut.mul_apply,h,ih,pow_succ']
    exact (mul_assoc _ _ _).symm

private theorem root_action (e : pointLocalSL F) (he : e ∈ pointRadicalSL F)
    (v : Fin 3 → F) : e.val.val.mulVec v = shear (e.val.val 0 1) (e.val.val 0 2) v := by
  obtain ⟨h00,h10,h20⟩ := (mem_pointLocalSL_iff F e).mp e.property
  obtain ⟨h11,h12,h21,h22⟩ := (mem_pointRadicalSL_iff F e).mp he
  ext i
  fin_cases i <;> simp [mulVec,dotProduct,Fin.sum_univ_three,shear,h00,h10,h20,h11,h12,h21,h22]

private theorem scalar_eq_one_of_coprime [Finite F] (a : F) {r : ℕ}
    (hr : 0 < r) (hc : Nat.Coprime r (Nat.card F - 1)) (ha : a ^ r = 1) : a = 1 := by
  have ha0 : a ≠ 0 := by intro hz; simp [hz, Nat.ne_of_gt hr] at ha
  let := Fintype.ofFinite F
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes hc (orderOf_dvd_of_pow_eq_one ha)
  exact orderOf_dvd_of_pow_eq_one (by
    simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card_sub_one_eq_one a ha0)

/-- Odd actors centralizing the actual point section are trivial when their order
is coprime to the scalar order. This includes arbitrary additive automorphisms. -/
theorem odd_coprime_point_section_eq_one [Finite F] [CharP F 2]
    (b : MulAut (Multiplicative (Fin 3 → F))) {r : ℕ}
    (ho : Odd r) (hco : Nat.Coprime r (Nat.card F - 1)) (hr : b ^ r = 1)
    (hc : ∀ g ∈ pointLocalSL F, ⁅b,naturalAut g⁆ ∈
      ((pointRadicalSL F).map (pointLocalSL F).subtype).map naturalAut) : b = 1 := by
  let f : (Fin 3 → F) →+ (Fin 3 → F) := {
    toFun := fun v => (b (Multiplicative.ofAdd v)).toAdd
    map_zero' := by exact congrArg Multiplicative.toAdd b.map_one
    map_add' := fun x y => congrArg Multiplicative.toAdd (b.map_mul _ _) }
  have ht (i j : Fin 3) (hij : i ≠ j) (hj : j ≠ 0) (t : F) :
      ∃ a d : F, ∀ (v : Fin 3 → F), f (v + Pi.single i (t * v j)) =
        shear a d (f v + Pi.single i (t * f v j)) := by
    let g := SpecialLinearGroup.transvection hij t
    have hg : g ∈ pointLocalSL F := by
      rw [mem_pointLocalSL_iff]
      simp [g,SpecialLinearGroup.transvection_coe,hj]
    obtain ⟨e,⟨e',he',hee'⟩,he⟩ := hc g hg
    subst e
    change naturalAut (e' : SL(3,F)) = ⁅b,naturalAut g⁆ at he
    have hh : b * naturalAut g = naturalAut e' * (naturalAut g * b) := by
      rw [he]
      simp only [commutatorElement_def,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one]
    refine ⟨e'.val.val 0 1,e'.val.val 0 2,fun v => ?_⟩
    have hv := congrArg (fun a : MulAut (Multiplicative (Fin 3 → F)) =>
      (a (Multiplicative.ofAdd v)).toAdd) hh
    change f (g.val.mulVec v) = e'.val.val.mulVec (g.val.mulVec (f v)) at hv
    rw [root_action e' he',transvection_action hij t,transvection_action hij t] at hv
    exact hv
  obtain ⟨a,ha⟩ := quotient_scalar f ht
  have ha1 : a = 1 := by
    apply scalar_eq_one_of_coprime a ho.pos hco
    have hh := pow_coordinate b 1 a (fun v => (ha v.toAdd).1) r
      (Multiplicative.ofAdd (Pi.single 1 1))
    simpa [hr] using hh.symm
  have hb : ∀ v, f v 1 = v 1 ∧ f v 2 = v 2 := by simpa [ha1] using ha
  obtain ⟨a,d,e,hf⟩ := first_row_linear f ht hb
  have haxis (z : F) : b (Multiplicative.ofAdd (Pi.single 0 z)) =
      Multiplicative.ofAdd (Pi.single 0 (a*z)) := by
    apply Multiplicative.toAdd.injective
    change f (Pi.single 0 z) = _
    rw [hf]
    ext i
    fin_cases i <;> simp
  have hp (m : ℕ) (z : F) : (b^m) (Multiplicative.ofAdd (Pi.single 0 z)) =
      Multiplicative.ofAdd (Pi.single 0 (a^m*z)) := by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ',MulAut.mul_apply,ih,haxis,pow_succ',mul_assoc]
  have ha1 : a = 1 := by
    apply scalar_eq_one_of_coprime a ho.pos hco
    have hh := congrArg (fun x : Multiplicative (Fin 3 → F) => x.toAdd 0) (hp r 1)
    simpa [hr] using hh.symm
  have htwo : b ^ 2 = 1 := by
    apply MulEquiv.ext
    intro v
    apply Multiplicative.toAdd.injective
    change f (f v.toAdd) = v.toAdd
    rw [hf,hf,ha1]
    ext i
    fin_cases i <;> simp [add_assoc]
    simpa only [add_assoc] using CharTwo.add_self_eq_zero (d * v.toAdd 1 + e * v.toAdd 2)
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes ho.coprime_two_right
    (orderOf_dvd_of_pow_eq_one hr) (orderOf_dvd_of_pow_eq_one htwo)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.LinearAction
