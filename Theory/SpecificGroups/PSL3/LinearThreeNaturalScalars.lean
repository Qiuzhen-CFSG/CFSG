module
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCores
public import Theory.GroupTheory.TwoCoreSectionCentralizerTransport

/-!
# Moving scalars for the natural SL₃ parabolic modules

The diagonal matrices diag(a,a,a⁻²) normalize the literal plane local and
act trivially on its quotient by O₂. Flag duality gives the point local.
In characteristic two, a nonidentity a makes all three diagonal entries
nonidentity, so both the natural and dual fixed spaces vanish. Cauchy's
theorem chooses a scalar of every prime order dividing the field-unit order.
In particular this includes the cubic center over the field of four elements;
no passage to PSL₃ or movement of the unipotent radical is asserted.

Source: Aschbacher--Smith, 10.2.9, printed p.751, the constrained rank-one
containing-model torus obstruction. These model facts concern the actual
natural representation and both literal parabolic residuals.
-/

@[expose] public section
open Matrix Subgroup
open scoped MatrixGroups commutatorElement
namespace Matrix.PSL3.LinearThree.Scalar
variable (F : Type*) [Field F]

def lineTorus : Fˣ →* SL(3,F) where
  toFun a := ⟨diagonal ![(a : F),(a : F),((a⁻¹)^2 : Fˣ)], by
    simp [det_diagonal, Fin.prod_univ_three, pow_two, mul_assoc]⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    change diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp [mul_pow, mul_comm]

theorem lineTorus_injective : Function.Injective (lineTorus F) := by
  intro a b h
  apply Units.ext
  exact congrArg (fun g : SL(3,F) => g.val 0 0) h

theorem lineTorus_val (a : Fˣ) :
    (lineTorus F a).val = diagonal ![(a : F),(a : F),((a⁻¹)^2 : Fˣ)] := rfl

theorem lineTorus_conj_entry (a : Fˣ) (g : SL(3,F)) (i j : Fin 3) :
    (lineTorus F a * g * (lineTorus F a)⁻¹).val i j =
      (![(a : F),(a : F),((a⁻¹)^2 : Fˣ)] i) * g.val i j *
        (![((a⁻¹ : Fˣ) : F),((a⁻¹ : Fˣ) : F),((a^2 : Fˣ) : F)] j) := by
  rw [←map_inv, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul,
    lineTorus_val, lineTorus_val, inv_inv, mul_diagonal, diagonal_mul]

theorem lineTorus_normalizes (a : Fˣ) :
    lineTorus F a ∈ normalizer (lineLocalSL F : Set SL(3,F)) := by
  have h (b : Fˣ) (g : SL(3,F)) (hg : g ∈ lineLocalSL F) :
      lineTorus F b * g * (lineTorus F b)⁻¹ ∈ lineLocalSL F := by
    rw [mem_lineLocalSL_iff] at hg ⊢
    simp [lineTorus_conj_entry,hg.1,hg.2.1,hg.2.2]
  rw [mem_normalizer_iff]
  intro g
  constructor
  · exact h a g
  · intro hg
    have hh := h a⁻¹ _ hg
    simpa only [map_inv,inv_inv,inv_mul_cancel_left,mul_inv_cancel_right,mul_assoc,inv_mul_cancel,mul_one] using hh

variable [Finite F] [CharP F 2]

theorem lineTorus_commutator (a : Fˣ) (g : lineLocalSL F) :
    ⁅lineTorus F a,(g : SL(3,F))⁆ ∈ (lineLocalSL F).pCoreIn 2 := by
  have hn := lineTorus_normalizes F a
  let h : lineLocalSL F := ⟨lineTorus F a * g * (lineTorus F a)⁻¹,
    (mem_normalizer_iff.mp hn g).mp g.property⟩
  let f := (SemidirectProduct.rightHom : Matrix.SL2.Affine F →* SL(2,F)).comp
    (lineLocalAffineEquiv F).toMonoidHom
  have hf : f h = f g := by
    apply Subtype.ext
    change !![(lineTorus F a * g * (lineTorus F a)⁻¹).val 0 0,
      (lineTorus F a * g * (lineTorus F a)⁻¹).val 0 1;
      (lineTorus F a * g * (lineTorus F a)⁻¹).val 1 0,
      (lineTorus F a * g * (lineTorus F a)⁻¹).val 1 1] =
        !![g.val.val 0 0,g.val.val 0 1;g.val.val 1 0,g.val.val 1 1]
    simp only [lineTorus_conj_entry]
    simp [mul_comm]
  have hc : h*g⁻¹ ∈ pCore 2 (lineLocalSL F) := by
    rw [lineLocalSL_twoCore_eq]
    change f (h*g⁻¹) = 1
    rw [map_mul,map_inv,hf,mul_inv_cancel]
  exact mem_map_of_mem (lineLocalSL F).subtype hc

theorem lineTorus_section (a : Fˣ) :
    lineTorus F a ∈ commutatorPreimage (normalizer (lineLocalSL F : Set SL(3,F)))
      (lineLocalSL F) ((lineLocalSL F).pCoreIn 2) := by
  have hn : (lineTorus F).range ≤ normalizer (lineLocalSL F : Set SL(3,F)) := by
    rintro _ ⟨b,rfl⟩
    exact lineTorus_normalizes F b
  apply le_commutatorPreimage hn ?_ (show lineTorus F a ∈ (lineTorus F).range from ⟨a,rfl⟩)
  apply commutator_le.mpr
  rintro _ ⟨b,rfl⟩ g hg
  exact lineTorus_commutator F b ⟨g,hg⟩


omit [Finite F] in
theorem lineTorus_fixed_eq_zero {a : Fˣ} (ha : a ≠ 1)
    (v : Fin 3 → F) (hv : (lineTorus F a).val.mulVec v = v) : v = 0 := by
  have haF : (a : F) ≠ 1 := fun h => ha (Units.ext h)
  have hbF : (((a⁻¹)^2 : Fˣ) : F) ≠ 1 := by
    intro h
    have hh : (a⁻¹ : Fˣ) = 1 := by
      apply Units.ext
      change ((a⁻¹ : Fˣ) : F) = 1
      exact (sq_eq_one_iff.mp h).elim id (fun he => by simpa only [CharTwo.neg_eq] using he)
    exact ha (inv_eq_one.mp hh)
  funext i
  have he : (![(a : F),(a : F),((a⁻¹)^2 : Fˣ)] i) * v i = v i := by
    simpa [lineTorus_val,Matrix.mulVec,dotProduct,diagonal] using congrFun hv i
  have hz : ![(a : F),(a : F),((a⁻¹)^2 : Fˣ)] i ≠ 1 := by
    fin_cases i <;> assumption
  by_contra hne
  exact hz ((mul_eq_right₀ hne).mp he)

def pointTorus : Fˣ →* SL(3,F) := (flagDuality F).toMonoidHom.comp (lineTorus F)

omit [Finite F] [CharP F 2] in
theorem pointTorus_injective : Function.Injective (pointTorus F) :=
  (flagDuality F).injective.comp (lineTorus_injective F)

omit [Finite F] [CharP F 2] in
theorem pointTorus_val (a : Fˣ) : (pointTorus F a).val =
    diagonal ![((a^2 : Fˣ) : F),((a⁻¹ : Fˣ) : F),((a⁻¹ : Fˣ) : F)] := by
  change ((lineTorus F a)⁻¹).val.transpose.submatrix Fin.rev Fin.rev = _
  rw [←map_inv,lineTorus_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem pointTorus_section (a : Fˣ) :
    pointTorus F a ∈ commutatorPreimage (normalizer (pointLocalSL F : Set SL(3,F)))
      (pointLocalSL F) ((pointLocalSL F).pCoreIn 2) := by
  have he : (lineLocalSL F).map (flagDuality F).toMonoidHom = pointLocalSL F := by
    apply le_antisymm
    · rintro _ ⟨g,hg,rfl⟩
      exact flagDuality_line_mem F ⟨g,hg⟩
    · intro g hg
      exact ⟨_,flagDuality_point_mem F ⟨g,hg⟩,(flagDuality F).right_inv g⟩
  have hh := twoCoreSectionCentralizer_map_equiv_le (lineLocalSL F) (flagDuality F)
    (mem_map_of_mem (flagDuality F).toMonoidHom (lineTorus_section F a))
  simpa only [he,pointTorus,MonoidHom.comp_apply] using hh

omit [Finite F] in
theorem pointTorus_fixed_eq_zero {a : Fˣ} (ha : a ≠ 1)
    (v : Fin 3 → F) (hv : (pointTorus F a).val.mulVec v = v) : v = 0 := by
  have haF : ((a⁻¹ : Fˣ) : F) ≠ 1 := fun h => ha (inv_eq_one.mp (Units.ext h))
  have hbF : ((a^2 : Fˣ) : F) ≠ 1 := by
    intro h
    apply ha
    apply Units.ext
    change (a : F) = 1
    exact (sq_eq_one_iff.mp h).elim id (fun he => by simpa only [CharTwo.neg_eq] using he)
  funext i
  have he : (![((a^2 : Fˣ) : F),((a⁻¹ : Fˣ) : F),((a⁻¹ : Fˣ) : F)] i) * v i = v i := by
    simpa [pointTorus_val,Matrix.mulVec,dotProduct,diagonal] using congrFun hv i
  have hz : ![((a^2 : Fˣ) : F),((a⁻¹ : Fˣ) : F),((a⁻¹ : Fˣ) : F)] i ≠ 1 := by
    fin_cases i <;> assumption
  by_contra hne
  exact hz ((mul_eq_right₀ hne).mp he)

omit [Finite F] in
theorem lineTorus_dual_fixed_eq_zero {a : Fˣ} (ha : a ≠ 1)
    (v : Fin 3 → F) (hv : (lineTorus F a)⁻¹.val.transpose.mulVec v = v) : v = 0 := by
  have he : (lineTorus F a)⁻¹.val.transpose = (lineTorus F a⁻¹).val := by
    rw [←map_inv,lineTorus_val,diagonal_transpose]
  rw [he] at hv
  exact lineTorus_fixed_eq_zero F (fun h => ha (inv_eq_one.mp h)) v hv

omit [Finite F] in
theorem pointTorus_dual_fixed_eq_zero {a : Fˣ} (ha : a ≠ 1)
    (v : Fin 3 → F) (hv : (pointTorus F a)⁻¹.val.transpose.mulVec v = v) : v = 0 := by
  have he : (pointTorus F a)⁻¹.val.transpose = (pointTorus F a⁻¹).val := by
    rw [←map_inv,pointTorus_val,diagonal_transpose]
  rw [he] at hv
  exact pointTorus_fixed_eq_zero F (fun h => ha (inv_eq_one.mp h)) v hv

/-- A scalar of any prescribed prime order moves every nonzero natural vector. -/
theorem exists_line_scalar (p : ℕ) [Fact p.Prime] (hp : p ∣ Nat.card F - 1) :
    ∃ x : SL(3,F), orderOf x = p ∧
      x ∈ commutatorPreimage (normalizer (lineLocalSL F : Set SL(3,F)))
        (lineLocalSL F) ((lineLocalSL F).pCoreIn 2) ∧
      (∀ v : Fin 3 → F, x.val.mulVec v = v → v = 0) ∧
      (∀ v : Fin 3 → F, x⁻¹.val.transpose.mulVec v = v → v = 0) := by
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by
    simpa only [Nat.card_units] using hp)
  have hne : a ≠ 1 := by
    intro he
    rw [he,orderOf_one] at ha
    exact (Fact.out : p.Prime).ne_one ha.symm
  exact ⟨lineTorus F a,(orderOf_injective (lineTorus F) (lineTorus_injective F) a).trans ha,
    lineTorus_section F a,lineTorus_fixed_eq_zero F hne,lineTorus_dual_fixed_eq_zero F hne⟩

/-- The opposite parabolic has the same prime-order fixed-point-free scalar. -/
theorem exists_point_scalar (p : ℕ) [Fact p.Prime] (hp : p ∣ Nat.card F - 1) :
    ∃ x : SL(3,F), orderOf x = p ∧
      x ∈ commutatorPreimage (normalizer (pointLocalSL F : Set SL(3,F)))
        (pointLocalSL F) ((pointLocalSL F).pCoreIn 2) ∧
      (∀ v : Fin 3 → F, x.val.mulVec v = v → v = 0) ∧
      (∀ v : Fin 3 → F, x⁻¹.val.transpose.mulVec v = v → v = 0) := by
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p (by
    simpa only [Nat.card_units] using hp)
  have hne : a ≠ 1 := by
    intro he
    rw [he,orderOf_one] at ha
    exact (Fact.out : p.Prime).ne_one ha.symm
  exact ⟨pointTorus F a,(orderOf_injective (pointTorus F) (pointTorus_injective F) a).trans ha,
    pointTorus_section F a,pointTorus_fixed_eq_zero F hne,pointTorus_dual_fixed_eq_zero F hne⟩

end Matrix.PSL3.LinearThree.Scalar
