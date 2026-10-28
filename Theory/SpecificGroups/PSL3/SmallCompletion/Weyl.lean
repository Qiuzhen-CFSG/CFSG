module
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient

/-!
# The native A₂ Weyl relation over fields of characteristic two

The full inverse image of the split projective torus is the determinant-one
matrix torus, including every cubic scalar. A regular diagonal element forces
each row of a torus-normalizing matrix to have only one nonzero entry. Inside
either marked parabolic this leaves exactly two Weyl cosets. Products of the
two nontrivial cosets are monomial three-cycles and have cube one already in
SL₃, hence in the actual projective quotient.

This is the native matrix calculation used to compare twisted markings in the
F.4.8 recognition route (Aschbacher–Smith, `refs/quasithin.pdf`, pp.278–279).
It does not replace the source F.4.49 relation modulo the Hall odd subgroup.
Both orientations and the field of order four are included.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
namespace Matrix.PSL3.SmallCompletion
variable (F : Type*) [Field F]

/-- The two simple coordinate reflections, in the point/line convention. -/
def reflectionSL [CharP F 2] (i : Bool) : SL(3,F) :=
  if i then ⟨!![0,1,0; 1,0,0; 0,0,1], by simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩
  else ⟨!![1,0,0; 0,0,1; 0,1,0], by simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩

def reflection [CharP F 2] (i : Bool) : PSL(3,F) := projection F (reflectionSL F i)

/-- Exact diagonal membership before the scalar quotient. -/
theorem mem_torusSL_iff (g : SL(3,F)) :
    g ∈ (torusSL F).range ↔ ∀ i j, i ≠ j → g.val i j = 0 := by
  constructor
  · rintro ⟨d,rfl⟩ i j hij
    simp [torusSL_val, Matrix.diagonal_apply_ne _ hij]
  · intro hz
    have h01 := hz 0 1 (by decide)
    have h02 := hz 0 2 (by decide)
    have h10 := hz 1 0 (by decide)
    have h12 := hz 1 2 (by decide)
    have h20 := hz 2 0 (by decide)
    have h21 := hz 2 1 (by decide)
    have hd : g.val 0 0 * g.val 1 1 * g.val 2 2 = 1 := by
      have h := g.property
      rw [Matrix.det_fin_three,h10,h20,h21] at h
      simpa only [zero_mul,mul_zero,add_zero,sub_zero] using h
    have h00 : g.val 0 0 ≠ 0 := by intro h; simp [h] at hd
    have h22 : g.val 2 2 ≠ 0 := by intro h; simp [h] at hd
    have h11 : g.val 1 1 = (g.val 0 0 * g.val 2 2)⁻¹ := by
      apply mul_left_cancel₀ (mul_ne_zero h00 h22)
      rw [mul_inv_cancel₀ (mul_ne_zero h00 h22)]
      simpa only [mul_assoc,mul_left_comm,mul_comm] using hd
    refine ⟨(Units.mk0 _ h00, Units.mk0 _ h22), ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [torusSL_val,h01,h02,h10,h12,h20,h21,h11]

/-- The full scalar kernel is contained in the diagonal torus. -/
theorem projection_ker_le_torusSL : (projection F).ker ≤ (torusSL F).range := by
  intro g hg
  obtain ⟨r,_,hr⟩ := SpecialLinearGroup.mem_center_iff.mp ((projection_ker F) ▸ hg)
  apply (mem_torusSL_iff F g).mpr
  intro i j hij
  rw [←hr]
  simp [Matrix.scalar, Matrix.diagonal_apply_ne _ hij]

/-- No scalar ambiguity is discarded when lifting projective torus membership. -/
theorem torus_comap : (torus F).comap (projection F) = (torusSL F).range := by
  change ((projection F).comp (torusSL F)).range.comap _ = _
  rw [MonoidHom.range_comp]
  exact Subgroup.comap_map_eq_self (projection_ker_le_torusSL F)

theorem mem_torusSL_iff_entries (g : SL(3,F)) :
    g ∈ (torusSL F).range ↔ g.val 0 1 = 0 ∧ g.val 0 2 = 0 ∧
      g.val 1 0 = 0 ∧ g.val 1 2 = 0 ∧ g.val 2 0 = 0 ∧ g.val 2 1 = 0 := by
  rw [mem_torusSL_iff]
  constructor
  · intro h
    exact ⟨h 0 1 (by decide),h 0 2 (by decide),h 1 0 (by decide),
      h 1 2 (by decide),h 2 0 (by decide),h 2 1 (by decide)⟩
  · rintro ⟨h01,h02,h10,h12,h20,h21⟩ i j hij
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | assumption

variable [CharP F 2]

theorem reflectionSL_sq (i : Bool) : reflectionSL F i ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  change (reflectionSL F i).val * (reflectionSL F i).val = 1
  cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    simp [reflectionSL,Matrix.mul_apply,Fin.sum_univ_three]

theorem reflection_sq (i : Bool) : reflection F i ^ 2 = 1 := by
  rw [reflection, ←map_pow, reflectionSL_sq, map_one]

omit [CharP F 2] in
private theorem cyclic_matrix_cube (x y z : F) :
    (!![0,x,0; 0,0,y; z,0,0] : Matrix (Fin 3) (Fin 3) F)^3 =
      Matrix.scalar (Fin 3) (x*y*z) := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [pow_succ,Matrix.mul_apply,Fin.sum_univ_three,Matrix.scalar] <;> ring

private theorem twisted_product_val (d e : Fˣ × Fˣ) :
    (torusSL F d * reflectionSL F false * (torusSL F e * reflectionSL F true)).val =
      !![0,(d.1 : F)*e.1,0; 0,0,(↑((d.1*d.2)⁻¹) : F)*e.2;
        (d.2 : F)*↑((e.1*e.2)⁻¹),0,0] := by
  change (torusSL F d).val * (reflectionSL F false).val *
    ((torusSL F e).val * (reflectionSL F true).val) = _
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [torusSL_val,reflectionSL,Matrix.mul_apply,Fin.sum_univ_three]

private theorem twisted_cube_false (d e : Fˣ × Fˣ) :
    (torusSL F d * reflectionSL F false * (torusSL F e * reflectionSL F true))^3 = 1 := by
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_pow,twisted_product_val,cyclic_matrix_cube]
  have h : ((d.1 : F)*e.1) * ((↑((d.1*d.2)⁻¹) : F)*e.2) *
      ((d.2 : F)*↑((e.1*e.2)⁻¹)) = 1 := by
    simp only [Units.val_inv_eq_inv_val,Units.val_mul]
    field_simp
  rw [h]
  simp

/-- Every diagonal twist of a three-cycle has cube one in SL₃ itself. -/
theorem twisted_reflectionsSL_cube (i : Bool) (d e : Fˣ × Fˣ) :
    (torusSL F d * reflectionSL F i * (torusSL F e * reflectionSL F (!i)))^3 = 1 := by
  cases i
  · exact twisted_cube_false F d e
  · let x := torusSL F d * reflectionSL F true
    let y := torusSL F e * reflectionSL F false
    have h : (y*x)^3 = 1 := twisted_cube_false F e d
    change (x*y)^3 = 1
    have he : (x*y)^3 = x * (y*x)^3 * x⁻¹ := by simp only [pow_succ,pow_zero]; group
    rw [he,h]
    simp

/-- The cubic identity descends through the actual projective quotient. -/
theorem twisted_reflections_cube (i : Bool) (d e : Fˣ × Fˣ) :
    (torusMap F d * reflection F i * (torusMap F e * reflection F (!i)))^3 = 1 := by
  change (projection F (torusSL F d) * projection F (reflectionSL F i) *
    (projection F (torusSL F e) * projection F (reflectionSL F (!i))))^3 = 1
  rw [←map_mul,←map_mul,←map_mul,←map_pow,twisted_reflectionsSL_cube,map_one]

/-- A normalizer of the full projective torus has at most one nonzero entry
in each row, once a regular diagonal element is available. -/
theorem normalizer_row_sparse (a : Fˣ) (ha : a ≠ 1) (g : SL(3,F))
    (hg : projection F g ∈ normalizer (torus F : Set PSL(3,F))) :
    ∀ i j k, g.val i j ≠ 0 → g.val i k ≠ 0 → j = k := by
  let d : Fˣ × Fˣ := (a,1)
  have hdiag : g * torusSL F d * g⁻¹ ∈ (torusSL F).range := by
    rw [←torus_comap]
    change projection F (g * torusSL F d * g⁻¹) ∈ torus F
    simpa only [map_mul,map_inv,torusMap,MonoidHom.comp_apply] using
      (Subgroup.mem_normalizer_iff.mp hg (torusMap F d)).mp ⟨d,rfl⟩
  obtain ⟨e,he⟩ := hdiag
  have heq : g.val * (torusSL F d).val = (torusSL F e).val * g.val := by
    have h : g * torusSL F d = torusSL F e * g := by rw [he]; group
    exact congrArg Subtype.val h
  have hentries (i j : Fin 3) :
      g.val i j * (![↑a,↑a⁻¹,1] j : F) =
        (![(e.1 : F),↑(e.1 * e.2)⁻¹,(e.2 : F)] i) * g.val i j := by
    simpa [torusSL_val, d, Matrix.mul_diagonal, Matrix.diagonal_mul] using
      congrFun (congrFun heq i) j
  have hinj : Function.Injective (![↑a,↑a⁻¹,1] : Fin 3 → F) := by
    have h1 : (a : F) ≠ 1 := fun h => ha (Units.ext h)
    have hi : (↑a⁻¹ : F) ≠ 1 := by
      intro h
      exact ha (inv_eq_one.mp (Units.ext h))
    have hne : (a : F) ≠ ↑a⁻¹ := by
      intro h
      have hs : (a : F)^2 = 1 := by rw [pow_two]; nth_rw 1 [h]; simp
      have hh : (a : F) = 1 := by
        have hh := mul_self_eq_one_iff.mp (show (a : F) * a = 1 by simpa [pow_two] using hs)
        rcases hh with hh | hh
        · exact hh
        · simpa only [CharTwo.neg_eq] using hh
      exact h1 hh
    intro j k hjk
    fin_cases j <;> fin_cases k <;> first
    | rfl
    | exact (h1 hjk).elim
    | exact (h1 hjk.symm).elim
    | exact (hi hjk).elim
    | exact (hi hjk.symm).elim
    | exact (hne hjk).elim
    | exact (hne hjk.symm).elim
  intro i j k hj hk
  apply hinj
  have h (l : Fin 3) (hl : g.val i l ≠ 0) :
      (![↑a,↑a⁻¹,1] l : F) = ![(e.1 : F),↑(e.1 * e.2)⁻¹,(e.2 : F)] i := by
    apply mul_left_cancel₀ hl
    simpa only [mul_comm] using hentries i l
  exact (h j hj).trans (h k hk).symm


/-- The coordinate reflection normalizes the actual projective torus. -/
theorem reflection_normalizes_torus (i : Bool) :
    reflection F i ∈ normalizer (torus F : Set PSL(3,F)) := by
  have hs : (reflection F i)⁻¹ = reflection F i :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using reflection_sq F i)
  have hf (x : PSL(3,F)) (hx : x ∈ torus F) :
      reflection F i * x * (reflection F i)⁻¹ ∈ torus F := by
    obtain ⟨d,rfl⟩ := hx
    let e : Fˣ × Fˣ := if i then ((d.1*d.2)⁻¹,d.2) else (d.1,(d.1*d.2)⁻¹)
    refine ⟨e,?_⟩
    rw [hs]
    change projection F (torusSL F e) =
      projection F (reflectionSL F i) * projection F (torusSL F d) *
        projection F (reflectionSL F i)
    rw [←map_mul,←map_mul]
    congr 1
    apply Subtype.ext
    change (torusSL F e).val = (reflectionSL F i).val * (torusSL F d).val * (reflectionSL F i).val
    cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;>
      simp [e,torusSL_val,reflectionSL,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three,mul_comm]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hf x,fun hx => ?_⟩
  have hh := hf _ hx
  have hrr : reflection F i * reflection F i = 1 := by
    simpa only [pow_two] using reflection_sq F i
  have he : reflection F i * (reflection F i * x * (reflection F i)⁻¹) *
      (reflection F i)⁻¹ = x := by
    rw [hs]
    calc
      _ = (reflection F i * reflection F i) * x *
          (reflection F i * reflection F i) := by group
      _ = x := by rw [hrr]; simp
  rwa [he] at hh

variable [Finite F]

/-- The native endpoints, with false denoting the point type. -/
def parabolic (i : Bool) : Subgroup PSL(3,F) :=
  if i then lineParabolic F else pointParabolic F

def parabolicSL (i : Bool) : Subgroup SL(3,F) :=
  if i then lineParabolicSL F else pointParabolicSL F

theorem reflection_mem (i : Bool) : reflection F i ∈ parabolic F i := by
  cases i
  · exact mem_map_of_mem _ ((mem_pointParabolicSL_iff F _).mpr (by simp [reflectionSL]))
  · exact mem_map_of_mem _ ((mem_lineParabolicSL_iff F _).mpr (by simp [reflectionSL]))

theorem reflection_not_mem_borel (i : Bool) : reflection F i ∉ borel F := by
  change reflectionSL F i ∉ (borel F).comap (projection F)
  rw [borel_comap,mem_borelSL_iff]
  cases i <;> simp [reflectionSL]

omit [CharP F 2] in
private theorem regular_unit (hq : 2 < Nat.card F) : ∃ a : Fˣ, a ≠ 1 := by
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [Nat.card_units]; omega)
  exact exists_ne 1

/-- In a native parabolic the torus normalizer has just the two Weyl cosets. -/
theorem normalizerSL_two_cosets (hq : 2 < Nat.card F) (i : Bool) (g : SL(3,F))
    (hp : g ∈ parabolicSL F i)
    (hg : projection F g ∈ normalizer (torus F : Set PSL(3,F))) :
    g ∈ (torusSL F).range ∨ g * reflectionSL F i ∈ (torusSL F).range := by
  obtain ⟨a,ha⟩ := regular_unit F hq
  have hr := normalizer_row_sparse F a ha g hg
  have hz (i j k : Fin 3) (hj : g.val i j ≠ 0) (hjk : j ≠ k) : g.val i k = 0 := by
    by_contra hk
    exact hjk (hr i j k hj hk)
  have hd := g.property
  rw [Matrix.det_fin_three] at hd
  cases i
  · obtain ⟨h10,h20⟩ := (mem_pointParabolicSL_iff F g).mp hp
    simp only [h10,h20,mul_zero,zero_mul,sub_zero,add_zero] at hd
    have h00 : g.val 0 0 ≠ 0 := by intro h; simp [h] at hd
    have h01 := hz 0 0 1 h00 (by decide)
    have h02 := hz 0 0 2 h00 (by decide)
    by_cases h11 : g.val 1 1 = 0
    · have h12 : g.val 1 2 ≠ 0 := by intro h; simp [h11,h] at hd
      have h21 : g.val 2 1 ≠ 0 := by intro h; simp [h11,h] at hd
      have h22 := hz 2 1 2 h21 (by decide)
      right
      rw [mem_torusSL_iff_entries]
      change (g.val * (reflectionSL F false).val) 0 1 = 0 ∧ (g.val * (reflectionSL F false).val) 0 2 = 0 ∧ (g.val * (reflectionSL F false).val) 1 0 = 0 ∧ (g.val * (reflectionSL F false).val) 1 2 = 0 ∧ (g.val * (reflectionSL F false).val) 2 0 = 0 ∧ (g.val * (reflectionSL F false).val) 2 1 = 0
      simpa [reflectionSL,Matrix.mul_apply,Fin.sum_univ_three]
        using And.intro h02 (And.intro h01 (And.intro h10 (And.intro h11 (And.intro h20 h22))))
    · have h12 := hz 1 1 2 h11 (by decide)
      have h22 : g.val 2 2 ≠ 0 := by intro h; simp [h12,h] at hd
      have h21 := hz 2 2 1 h22 (by decide)
      left
      exact (mem_torusSL_iff_entries F g).mpr ⟨h01,h02,h10,h12,h20,h21⟩
  · obtain ⟨h20,h21⟩ := (mem_lineParabolicSL_iff F g).mp hp
    simp only [h20,h21,mul_zero,sub_zero,add_zero] at hd
    by_cases h00 : g.val 0 0 = 0
    · have h01 : g.val 0 1 ≠ 0 := by intro h; simp [h00,h] at hd
      have h10 : g.val 1 0 ≠ 0 := by intro h; simp [h00,h] at hd
      have h02 := hz 0 1 2 h01 (by decide)
      have h11 := hz 1 0 1 h10 (by decide)
      have h12 := hz 1 0 2 h10 (by decide)
      right
      rw [mem_torusSL_iff_entries]
      change (g.val * (reflectionSL F true).val) 0 1 = 0 ∧ (g.val * (reflectionSL F true).val) 0 2 = 0 ∧ (g.val * (reflectionSL F true).val) 1 0 = 0 ∧ (g.val * (reflectionSL F true).val) 1 2 = 0 ∧ (g.val * (reflectionSL F true).val) 2 0 = 0 ∧ (g.val * (reflectionSL F true).val) 2 1 = 0
      simpa [reflectionSL,Matrix.mul_apply,Fin.sum_univ_three]
        using And.intro h00 (And.intro h02 (And.intro h11 (And.intro h12 (And.intro h21 h20))))
    · have h01 := hz 0 0 1 h00 (by decide)
      have h02 := hz 0 0 2 h00 (by decide)
      have h11 : g.val 1 1 ≠ 0 := by intro h; simp [h01,h] at hd
      have h10 := hz 1 1 0 h11 (by decide)
      have h12 := hz 1 1 2 h11 (by decide)
      left
      exact (mem_torusSL_iff_entries F g).mpr ⟨h01,h02,h10,h12,h20,h21⟩

/-- Outside the whole Borel, a parabolic torus normalizer is a torus twist
of its specified reflection, also when the projective scalar kernel has order three. -/
theorem normalizer_eq_torus_mul_reflection (hq : 2 < Nat.card F) (i : Bool)
    (g : PSL(3,F)) (hp : g ∈ parabolic F i)
    (hg : g ∈ normalizer (torus F : Set PSL(3,F))) (hout : g ∉ borel F) :
    ∃ d : Fˣ × Fˣ, g = torusMap F d * reflection F i := by
  obtain ⟨x,rfl⟩ := projection_surjective F g
  have hx : x ∈ parabolicSL F i := by
    cases i
    · change x ∈ (pointParabolic F).comap (projection F) at hp
      rwa [pointParabolic_comap] at hp
    · change x ∈ (lineParabolic F).comap (projection F) at hp
      rwa [lineParabolic_comap] at hp
  rcases normalizerSL_two_cosets F hq i x hx hg with h | ⟨d,hd⟩
  · exact False.elim (hout (torus_le_borel F (by
      change x ∈ (torus F).comap (projection F)
      rwa [torus_comap])))
  · refine ⟨d,?_⟩
    change projection F x = projection F (torusSL F d) * projection F (reflectionSL F i)
    rw [←map_mul,hd]
    congr 1
    have h := reflectionSL_sq F i
    rw [pow_two] at h
    rw [mul_assoc,h,mul_one]

/-- The exact native cubic relation follows from torus normalization and
escape from the Borel; no prescribed order of the product is an input. -/
theorem normalizer_product_cube (hq : 2 < Nat.card F) (i : Bool)
    (s t : PSL(3,F)) (hs : s ∈ parabolic F i) (ht : t ∈ parabolic F (!i))
    (hsn : s ∈ normalizer (torus F : Set PSL(3,F)))
    (htn : t ∈ normalizer (torus F : Set PSL(3,F)))
    (hsout : s ∉ borel F) (htout : t ∉ borel F) : (s*t)^3 = 1 := by
  obtain ⟨d,rfl⟩ := normalizer_eq_torus_mul_reflection F hq i s hs hsn hsout
  obtain ⟨e,rfl⟩ := normalizer_eq_torus_mul_reflection F hq (!i) t ht htn htout
  exact twisted_reflections_cube F i d e

end Matrix.PSL3.SmallCompletion
