module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourOuter
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointRadicalSpecial

/-!
# The upper graph class in the unitary-four extension

Conjugating the graph involution by a unitary matrix gives a coboundary u
for which uJ is alternating. In the upper unitriangular subgroup this
forces the middle and top-right entries to vanish. The remaining radical
coordinates are fixed by the field involution. A trace-one scalar then
constructs an explicit radical conjugator to the original graph involution.

Thus graph-class elements in the marked upper extension are conjugate
already inside its ordinary upper subgroup. The distinct twisted outer
involution class is not included. This is the local graph-class transport
needed for Aschbacher--Smith F.4.35--36, printed p.292.
-/
@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups Subgroup
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourGraphPlacement
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourOuter
variable (F : Type*) [Field F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "J" => form F σ hσ
local notation "SU₄" => SU F J

omit [CharP F 2] in
private theorem inverse_matrix (g : SU₄) :
    (g⁻¹).val.val = gram F * (J).conjTranspose g.val.val * gram F := by
  have hu := g.property.1
  change (J).conjTranspose g.val.val * gram F * g.val.val = gram F at hu
  have hl : (gram F * (J).conjTranspose g.val.val * gram F) * g.val.val = 1 := by
    calc
      _ = gram F * ((J).conjTranspose g.val.val * gram F * g.val.val) := by
        simp only [mul_assoc]
      _ = 1 := by rw [hu, gram_sq]
  calc
    (g⁻¹).val.val = ((gram F * (J).conjTranspose g.val.val * gram F) *
        g.val.val) * (g⁻¹).val.val := by rw [hl, one_mul]
    _ = gram F * (J).conjTranspose g.val.val * gram F := by
      rw [mul_assoc, show g.val.val * (g⁻¹).val.val = 1 from g.val.val_inv, mul_one]

omit [CharP F 2] in
/-- The matrix associated to a graph coboundary is an alternating-form
congruence transform of the original Gram matrix. -/
theorem coboundary_gram (g : SU₄) :
    (g * (matrixAut F σ hσ g)⁻¹).val.val * gram F =
      g.val.val * gram F * g.val.val.transpose := by
  have hc : (J).conjTranspose (matrixAut F σ hσ g).val.val = g.val.val.transpose := by
    ext i j
    exact hσ _
  change (g.val.val * ((matrixAut F σ hσ g)⁻¹).val.val) * gram F = _
  rw [inverse_matrix, hc]
  simp only [mul_assoc, gram_sq, mul_one]

omit [CharP F 2] in
private theorem gram_transpose : (gram F).transpose = gram F := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

omit [CharP F 2] in
theorem coboundary_gram_symmetric (g : SU₄) :
    ((g * (matrixAut F σ hσ g)⁻¹).val.val * gram F).transpose =
      (g * (matrixAut F σ hσ g)⁻¹).val.val * gram F := by
  rw [coboundary_gram, transpose_mul, transpose_mul, transpose_transpose, gram_transpose,
    mul_assoc]

theorem coboundary_gram_diagonal (g : SU₄) (i : Fin 4) :
    ((g * (matrixAut F σ hσ g)⁻¹).val.val * gram F) i i = 0 := by
  rw [coboundary_gram]
  simp [gram, Matrix.mul_apply, Fin.sum_univ_succ, transpose_apply]
  ring_nf
  simp [CharTwo.two_eq_zero]

omit [CharP F 2] in
/-- A conjugate of the marked graph involution retains the graph coset
and has an actual unitary coboundary as its matrix coordinate. -/
theorem graph_conjugate_coordinates {f : Extension F σ hσ}
    (hf : IsConj (sigma F σ hσ) f) :
    f.right = generator ∧ ∃ g : SU₄, f.left = g * (matrixAut F σ hσ g)⁻¹ := by
  obtain ⟨h, hh⟩ := isConj_iff.mp hf
  have hr := SemidirectProduct.rightHom.map_isConj hf
  have hr' : f.right = generator := (isConj_iff_eq.mp hr).symm
  refine ⟨hr', h.left, ?_⟩
  have hc : (SemidirectProduct.inr h.right : Extension F σ hσ) * sigma F σ hσ *
      (SemidirectProduct.inr h.right)⁻¹ = sigma F σ hσ := by
    simp [sigma, ← map_mul, ← map_inv, mul_comm]
  have he : h * sigma F σ hσ * h⁻¹ =
      SemidirectProduct.inl h.left * sigma F σ hσ * (SemidirectProduct.inl h.left)⁻¹ := by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right h]
    calc
      _ = SemidirectProduct.inl h.left *
          ((SemidirectProduct.inr h.right : Extension F σ hσ) * sigma F σ hσ *
            (SemidirectProduct.inr h.right)⁻¹) * (SemidirectProduct.inl h.left)⁻¹ := by group
      _ = _ := by rw [hc]
  have hl := congrArg SemidirectProduct.left (hh.symm.trans he)
  simpa [sigma, action_generator, map_inv] using hl

private def traceCoordinates (c : RadicalCoordinates F σ) (ω : F)
    (hx : σ c.x = c.x) (hy : σ c.y = c.y) : RadicalCoordinates F σ where
  x := ω * c.x
  y := ω * c.y
  z := 0
  trace_eq := by
    simp only [map_zero, zero_add, map_mul, hx, hy]
    ring_nf
    simp [CharTwo.two_eq_zero]

private theorem traceCoordinates_coboundary (c : RadicalCoordinates F σ)
    (hx : σ c.x = c.x) (hy : σ c.y = c.y) (hz : c.z = 0)
    (ω : F) (hω : ω + σ ω = 1) :
    let v := radicalElement F σ hσ (traceCoordinates F σ c ω hx hy)
    v * (matrixAut F σ hσ v)⁻¹ = radicalElement F σ hσ c := by
  intro v
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  apply Units.ext
  change radicalMatrix F σ (traceCoordinates F σ c ω hx hy) =
    radicalMatrix F σ c * (radicalMatrix F σ (traceCoordinates F σ c ω hx hy)).map σ
  have hω' : σ ω = 1 + ω := by
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hω
  have hthree : (3 : F) = 1 := by
    calc
      (3 : F) = 2 + 1 := by norm_num
      _ = 1 := by rw [CharTwo.two_eq_zero, zero_add]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radicalMatrix, traceCoordinates, Matrix.mul_apply, Fin.sum_univ_succ,
      hx, hy, hz, hω'] <;>
    ring_nf <;> simp [CharTwo.two_eq_zero, hthree]


/-- Every graph-class element of the actual upper extension is conjugate
to the marked graph involution by an ordinary upper-unitriangular element. -/
theorem upper_graph_conjugator (hne : ∃ x : F, σ x ≠ x)
    {f : Extension F σ hσ} (hfU : f ∈ extendedUpper F σ hσ)
    (hf : IsConj (sigma F σ hσ) f) :
    ∃ v : SU₄, v ∈ UnitaryFourSylow.upper F σ hσ ∧
      (SemidirectProduct.inl v : Extension F σ hσ) * sigma F σ hσ *
        (SemidirectProduct.inl v)⁻¹ = f := by
  obtain ⟨hfr, g, hfg⟩ := graph_conjugate_coordinates F σ hσ hf
  have hdiag (i : Fin 4) : (f.left.val.val * gram F) i i = 0 := by
    rw [hfg]
    exact coboundary_gram_diagonal F σ hσ g i
  have h03 : f.left.val.val 0 3 = 0 := by
    simpa [gram, Matrix.mul_apply, Fin.sum_univ_succ] using hdiag 0
  have h12 : f.left.val.val 1 2 = 0 := by
    simpa [gram, Matrix.mul_apply, Fin.sum_univ_succ] using hdiag 1
  have hU : f.left ∈ UnitaryFourSylow.upper F σ hσ := hfU
  obtain ⟨ht, hd⟩ := (UnitaryFourSylow.mem_upper_iff_entries F σ hσ f.left).mp hU
  have hl : f.left ∈ localSU F J := (UnitaryFourSylow.mem_upper F σ hσ f.left).mp hU |>.1
  have hr : (⟨f.left, hl⟩ : localSU F J) ∈ radical F σ hσ :=
    (mem_radical F σ hσ _).mpr ⟨hd 1, h12, ht 2 1 (by decide), hd 2⟩
  obtain ⟨c, hc⟩ := (radicalCoordinatesEquiv F σ hσ).surjective ⟨⟨f.left, hl⟩, hr⟩
  have hc' : radicalElement F σ hσ c = f.left := congrArg (fun r : radical F σ hσ => r.val.val) hc
  have hz : c.z = 0 := by simpa [radicalElement, radicalMatrix] using
    (congrArg (fun a : SU₄ => a.val.val 0 3) hc').trans h03
  have hs : (f.left.val.val * gram F).transpose = f.left.val.val * gram F := by
    rw [hfg]
    exact coboundary_gram_symmetric F σ hσ g
  rw [← hc'] at hs
  have hx : σ c.x = c.x := by
    have hh := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 1 0) hs
    simpa [radicalElement, radicalMatrix, gram, Matrix.mul_apply, Fin.sum_univ_succ] using hh
  have hy : σ c.y = c.y := by
    have hh := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 2 0) hs
    simpa [radicalElement, radicalMatrix, gram, Matrix.mul_apply, Fin.sum_univ_succ] using hh
  obtain ⟨ω, hω⟩ := exists_trace_eq F σ hσ hne (1 : FixedBy.subfield F σ)
  let v := radicalElement F σ hσ (traceCoordinates F σ c ω hx hy)
  refine ⟨v, UnitaryFourSylow.radicalElement_mem_upper F σ hσ _, ?_⟩
  apply SemidirectProduct.ext
  · change (SemidirectProduct.inl v * sigma F σ hσ * (SemidirectProduct.inl v)⁻¹).left = f.left
    have hv := traceCoordinates_coboundary F σ hσ c hx hy hz ω hω
    have hc'' := hv.trans hc'
    simpa [sigma, action_generator, map_inv] using hc''
  · simp [sigma, hfr]

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourGraphPlacement
