module
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Image.Containment.Generators

/-!
# Normal generation of odd special unitary four-space

The signed plane Levi and plane radical normally generate the special unitary
group of the antidiagonal Hermitian form. Conjugating the radical by coordinate
reversal supplies the opposite roots. A nonzero skew scalar gives the signed
long-root Weyl elements. Elementary row operations first fix the first column,
then eliminate the remaining hyperbolic two-space; fixing the first two columns
leaves exactly the published plane radical.

The elimination argument works over any field with an involution and a nonzero
skew scalar. Over the actual quadratic extension GF(p^(2n)), the moving torus
supplies such a scalar. Combining normal generation with the already proved
commutator containment gives perfectness, including fixed-field order three.

Source: GLS3 §2.7, classical unitary matrix conventions; the twisted A₃/D₃
comparison used in Aschbacher–Smith A.2.17, printed pp.38–39 of
`refs/quasithin.pdf`. All matrices retain the signs of `Containment.Generators`.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.Minus.OddSixComparison.Image.Containment
namespace Generation
open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary UnitaryFourFlag
variable (E : Type*) [Field E] (σ : E ≃+* E) (hσ : Function.Involutive σ)

def reverse : (SU E (form E σ hσ)) :=
  ⟨⟨gram E, gram E, gram_sq E, gram_sq E⟩,
    (by ext i j; fin_cases i <;> fin_cases j <;>
      simp [form, gram, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_succ]),
    Units.ext (by
      change (gram E).det = 1
      rw [Matrix.det_succ_row_zero]
      simp [gram, Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
      norm_num)⟩

def lower (z b c : E) (hb : σ b = -b) (hc : σ c = -c) : (SU E (form E σ hσ)) :=
  reverse E σ hσ * upper E σ hσ z b c hb hc * (reverse E σ hσ)⁻¹

theorem lower_val (z b c : E) (hb : σ b = -b) (hc : σ c = -c) :
    (lower E σ hσ z b c hb hc).val.val =
      !![1,0,0,0; 0,1,0,0; -σ z,c,1,0; b,z,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lower, reverse, upper, upperMatrix, gram, Matrix.mul_apply, Fin.sum_univ_succ]

def short (t : E) : (SU E (form E σ hσ)) :=
  levi E σ hσ ⟨!![1,t;0,1], by simp [Matrix.det_fin_two]⟩

theorem short_val (t : E) : (short E σ hσ t).val.val =
    !![1,t,0,0; 0,1,0,0; 0,0,1,-σ t; 0,0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [short, levi, leviMatrix]

def pair : (SU E (form E σ hσ)) :=
  levi E σ hσ ⟨!![0,1;-1,0], by simp [Matrix.det_fin_two]⟩

theorem pair_val : (pair E σ hσ).val.val =
    !![0,1,0,0; -1,0,0,0; 0,0,0,-1; 0,0,1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pair, levi, leviMatrix]

def outerWeyl (s : E) (hs : σ s = -s) : (SU E (form E σ hσ)) :=
  upper E σ hσ 0 s 0 hs (by simp) *
    lower E σ hσ 0 (-s⁻¹) 0 (by simp [hs]) (by simp) *
    upper E σ hσ 0 s 0 hs (by simp)

theorem outerWeyl_val (s : E) (hs : σ s = -s) (hs0 : s ≠ 0) :
    (outerWeyl E σ hσ s hs).val.val =
      !![0,0,0,s; 0,1,0,0; 0,0,1,0; -s⁻¹,0,0,0] := by
  change (upper E σ hσ 0 s 0 hs _).val.val *
    (lower E σ hσ 0 (-s⁻¹) 0 _ _).val.val *
    (upper E σ hσ 0 s 0 hs _).val.val = _
  rw [lower_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperMatrix, Matrix.mul_apply, Fin.sum_univ_succ, hs0]

def middleWeyl (s : E) (hs : σ s = -s) : (SU E (form E σ hσ)) :=
  upper E σ hσ 0 0 s (by simp) hs *
    lower E σ hσ 0 0 (-s⁻¹) (by simp) (by simp [hs]) *
    upper E σ hσ 0 0 s (by simp) hs

theorem middleWeyl_val (s : E) (hs : σ s = -s) (hs0 : s ≠ 0) :
    (middleWeyl E σ hσ s hs).val.val =
      !![1,0,0,0; 0,0,s,0; 0,-s⁻¹,0,0; 0,0,0,1] := by
  change (upper E σ hσ 0 0 s _ hs).val.val *
    (lower E σ hσ 0 0 (-s⁻¹) _ _).val.val *
    (upper E σ hσ 0 0 s _ hs).val.val = _
  rw [lower_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperMatrix, Matrix.mul_apply, Fin.sum_univ_succ, hs0]

theorem column_pairing (g : (SU E (form E σ hσ))) (i j : Fin 4) :
    σ (g.val.val 0 i) * g.val.val 3 j + σ (g.val.val 1 i) * g.val.val 2 j +
      σ (g.val.val 2 i) * g.val.val 1 j + σ (g.val.val 3 i) * g.val.val 0 j =
        gram E i j := by
  have hu := congrArg (fun M : Matrix (Fin 4) (Fin 4) E => M i j) g.property.1
  change ((form E σ hσ).conjTranspose g.val.val * gram E * g.val.val) i j = _ at hu
  simp [form, gram, HermitianForm.conjTranspose, Matrix.mul_apply,
    Fin.sum_univ_succ] at hu ⊢
  linear_combination hu

variable (H : Subgroup (SU E (form E σ hσ))) [H.Normal]
variable (hL : ∀ A, levi E σ hσ A ∈ H)
variable (hU : ∀ z b c hb hc, upper E σ hσ z b c hb hc ∈ H)
include hU in
theorem lower_mem (z b c : E) (hb : σ b = -b) (hc : σ c = -c) :
    lower E σ hσ z b c hb hc ∈ H :=
  Subgroup.Normal.conj_mem inferInstance _ (hU z b c hb hc) _
include hL in
omit [H.Normal] in
theorem short_mem (t : E) : short E σ hσ t ∈ H := hL _
include hL in
omit [H.Normal] in
theorem pair_mem : pair E σ hσ ∈ H := hL _
include hU in
theorem outerWeyl_mem (s : E) (hs : σ s = -s) : outerWeyl E σ hσ s hs ∈ H :=
  H.mul_mem (H.mul_mem (hU _ _ _ _ _) (lower_mem E σ hσ H hU _ _ _ _ _))
    (hU _ _ _ _ _)
include hU in
theorem middleWeyl_mem (s : E) (hs : σ s = -s) : middleWeyl E σ hσ s hs ∈ H :=
  H.mul_mem (H.mul_mem (hU _ _ _ _ _) (lower_mem E σ hσ H hU _ _ _ _ _))
    (hU _ _ _ _ _)


def middleDiag (s : E) (hs : σ s = -s) (t : E) (ht : σ t = t) : (SU E (form E σ hσ)) :=
  middleWeyl E σ hσ (t * s) (by simp [ht, hs]) *
    middleWeyl E σ hσ (-s) (by simp [hs])

theorem middleDiag_val (s : E) (hs : σ s = -s) (hs0 : s ≠ 0)
    (t : E) (ht : σ t = t) (ht0 : t ≠ 0) :
    (middleDiag E σ hσ s hs t ht).val.val =
      !![1,0,0,0; 0,t,0,0; 0,0,t⁻¹,0; 0,0,0,1] := by
  change (middleWeyl E σ hσ (t * s) _).val.val *
    (middleWeyl E σ hσ (-s) _).val.val = _
  rw [middleWeyl_val E σ hσ _ _ (mul_ne_zero ht0 hs0),
    middleWeyl_val E σ hσ _ _ (neg_ne_zero.mpr hs0)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, hs0]
  field_simp

include hU in
theorem middleDiag_mem (s : E) (hs : σ s = -s) (t : E) (ht : σ t = t) :
    middleDiag E σ hσ s hs t ht ∈ H :=
  H.mul_mem (middleWeyl_mem E σ hσ H hU _ _) (middleWeyl_mem E σ hσ H hU _ _)

/-- The first fixed column forces the opposite row. -/
theorem last_row (g : (SU E (form E σ hσ))) (h0 : ∀ i, g.val.val i 0 = ![1,0,0,0] i) :
    ∀ j, g.val.val 3 j = ![0,0,0,1] j := by
  intro j
  have h := column_pairing E σ hσ g 0 j
  simpa [h0, gram] using h

include hU in
omit [H.Normal] in
theorem mem_of_fixed_plane (g : (SU E (form E σ hσ)))
    (h0 : ∀ i, g.val.val i 0 = ![1,0,0,0] i)
    (h1 : ∀ i, g.val.val i 1 = ![0,1,0,0] i) : g ∈ H := by
  have hr3 := last_row E σ hσ g h0
  have hr2 (j : Fin 4) : g.val.val 2 j = ![0,0,1,0] j := by
    have h := column_pairing E σ hσ g 1 j
    simpa [h1, gram] using h
  have hb : σ (g.val.val 0 3) = -g.val.val 0 3 := by
    have h := column_pairing E σ hσ g 3 3
    simp [hr2, hr3, gram] at h
    linear_combination h
  have hc : σ (g.val.val 1 2) = -g.val.val 1 2 := by
    have h := column_pairing E σ hσ g 2 2
    simp [hr2, hr3, gram] at h
    linear_combination h
  have hz : g.val.val 1 3 = -σ (g.val.val 0 2) := by
    have h := column_pairing E σ hσ g 2 3
    simp [hr2, hr3, gram] at h
    linear_combination h
  have he : g = upper E σ hσ (g.val.val 0 2) (g.val.val 0 3) (g.val.val 1 2) hb hc := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperMatrix, h0, h1, hr2, hr3, hz]
  rw [he]
  exact hU _ _ _ _ _

/-- Determinant and Hermitian equations for the remaining hyperbolic plane. -/
theorem middle_entries (g : (SU E (form E σ hσ))) (h0 : ∀ i, g.val.val i 0 = ![1,0,0,0] i) :
    g.val.val 1 1 * g.val.val 2 2 - g.val.val 1 2 * g.val.val 2 1 = 1 ∧
      σ (g.val.val 1 1) = g.val.val 1 1 ∧ σ (g.val.val 2 1) = -g.val.val 2 1 := by
  have hr := last_row E σ hσ g h0
  have hd : g.val.val.det = 1 := congrArg Units.val g.property.2
  rw [Matrix.det_succ_row_zero] at hd
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove, h0, hr] at hd
  have h11 := column_pairing E σ hσ g 1 1
  have h12 := column_pairing E σ hσ g 1 2
  simp [hr, gram] at h11 h12
  refine ⟨hd, ?_, ?_⟩
  · linear_combination g.val.val 1 1 * h12 - g.val.val 1 2 * h11 - σ (g.val.val 1 1) * hd
  · linear_combination -g.val.val 2 1 * h12 + g.val.val 2 2 * h11 - σ (g.val.val 2 1) * hd

include hL hU in
theorem mem_of_fixed_point_pivot (s : E) (hs : σ s = -s) (hs0 : s ≠ 0)
    (g : (SU E (form E σ hσ))) (h0 : ∀ i, g.val.val i 0 = ![1,0,0,0] i)
    (hd0 : g.val.val 1 1 ≠ 0) : g ∈ H := by
  have hr := last_row E σ hσ g h0
  obtain ⟨_, hd, hg⟩ := middle_entries E σ hσ g h0
  let c := -(g.val.val 2 1 / g.val.val 1 1)
  have hc : σ c = -c := by simp [c, hd, hg, neg_div]
  let l := lower E σ hσ 0 0 c (by simp) hc
  have hl : l ∈ H := lower_mem E σ hσ H hU _ _ _ _ _
  let g1 := l * g
  have h10 (i : Fin 4) : g1.val.val i 0 = ![1,0,0,0] i := by
    change (l.val.val * g.val.val) i 0 = _
    dsimp [l]
    rw [lower_val]
    fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, h0]
  have h11 (i : Fin 4) : g1.val.val i 1 = ![g.val.val 0 1,g.val.val 1 1,0,0] i := by
    change (l.val.val * g.val.val) i 1 = _
    dsimp [l]
    rw [lower_val]
    fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, hr, c, hd0]
  let u := short E σ hσ (-(g.val.val 0 1 / g.val.val 1 1))
  have hu : u ∈ H := short_mem E σ hσ H hL _
  let g2 := u * g1
  have h20 (i : Fin 4) : g2.val.val i 0 = ![1,0,0,0] i := by
    change (u.val.val * g1.val.val) i 0 = _
    dsimp [u]
    rw [short_val]
    fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, h10]
  have h21 (i : Fin 4) : g2.val.val i 1 = ![0,g.val.val 1 1,0,0] i := by
    change (u.val.val * g1.val.val) i 1 = _
    dsimp [u]
    rw [short_val]
    fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, h11, hd0]
  let d := middleDiag E σ hσ s hs (g.val.val 1 1)⁻¹ (by simp [hd])
  have hdH : d ∈ H := middleDiag_mem E σ hσ H hU _ _ _ _
  have hdv := middleDiag_val E σ hσ s hs hs0 (g.val.val 1 1)⁻¹ (by simp [hd])
    (inv_ne_zero hd0)
  have h30 (i : Fin 4) : (d * g2).val.val i 0 = ![1,0,0,0] i := by
    change (d.val.val * g2.val.val) i 0 = _
    rw [hdv]
    fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, h20]
  have h31 (i : Fin 4) : (d * g2).val.val i 1 = ![0,1,0,0] i := by
    change (d.val.val * g2.val.val) i 1 = _
    rw [hdv]
    fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, h21, hd0]
  have hmem := mem_of_fixed_plane E σ hσ H hU (d * g2) h30 h31
  exact (H.mul_mem_cancel_left hl).mp
    ((H.mul_mem_cancel_left hu).mp ((H.mul_mem_cancel_left hdH).mp hmem))

include hL hU in
theorem mem_of_fixed_point (s : E) (hs : σ s = -s) (hs0 : s ≠ 0)
    (g : (SU E (form E σ hσ))) (h0 : ∀ i, g.val.val i 0 = ![1,0,0,0] i) : g ∈ H := by
  by_cases hd : g.val.val 1 1 ≠ 0
  · exact mem_of_fixed_point_pivot E σ hσ H hL hU s hs hs0 g h0 hd
  have hg : g.val.val 2 1 ≠ 0 := by
    obtain ⟨he, _⟩ := middle_entries E σ hσ g h0
    intro hg
    simp_all
  let w := middleWeyl E σ hσ s hs
  have hw : w ∈ H := middleWeyl_mem E σ hσ H hU _ _
  have hwv := middleWeyl_val E σ hσ s hs hs0
  apply (H.mul_mem_cancel_left hw).mp
  apply mem_of_fixed_point_pivot E σ hσ H hL hU s hs hs0 (w * g)
  · intro i
    change (w.val.val * g.val.val) i 0 = _
    rw [hwv]
    fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, h0]
  · change (w.val.val * g.val.val) 1 1 ≠ 0
    rw [hwv]
    simpa [Matrix.mul_apply, Fin.sum_univ_succ] using mul_ne_zero hs0 hg

include hL hU in
theorem mem_of_last_entry (s : E) (hs : σ s = -s) (hs0 : s ≠ 0)
    (g : SU E (form E σ hσ)) (hd : g.val.val 3 0 ≠ 0) : g ∈ H := by
  have hss (x : E) : σ (σ x) = x := hσ x
  let t := short E σ hσ (σ (g.val.val 2 0 / g.val.val 3 0))
  have ht : t ∈ H := short_mem E σ hσ H hL _
  let g1 := t * g
  have h12 : g1.val.val 2 0 = 0 := by
    change (t.val.val * g.val.val) 2 0 = _
    dsimp [t]
    rw [short_val]
    simp [Matrix.mul_apply, Fin.sum_univ_succ, hss, hd]
  have h11 : g1.val.val 1 0 = g.val.val 1 0 := by
    change (t.val.val * g.val.val) 1 0 = _
    dsimp [t]
    rw [short_val]
    simp [Matrix.mul_apply, Fin.sum_univ_succ]
  have h13 : g1.val.val 3 0 = g.val.val 3 0 := by
    change (t.val.val * g.val.val) 3 0 = _
    dsimp [t]
    rw [short_val]
    simp [Matrix.mul_apply, Fin.sum_univ_succ]
  let u := upper E σ hσ (σ (g.val.val 1 0 / g.val.val 3 0)) 0 0 (by simp) (by simp)
  have hu : u ∈ H := hU _ _ _ _ _
  let g2 := u * g1
  have h21 : g2.val.val 1 0 = 0 := by
    change (u.val.val * g1.val.val) 1 0 = _
    simp [u, upper, upperMatrix, Matrix.mul_apply, Fin.sum_univ_succ, h11, h13, hss, hd]
  have h22 : g2.val.val 2 0 = 0 := by
    change (u.val.val * g1.val.val) 2 0 = _
    simp [u, upper, upperMatrix, Matrix.mul_apply, Fin.sum_univ_succ, h12]
  have h23 : g2.val.val 3 0 = g.val.val 3 0 := by
    change (u.val.val * g1.val.val) 3 0 = _
    simp [u, upper, upperMatrix, Matrix.mul_apply, Fin.sum_univ_succ, h13]
  let b := -(g2.val.val 0 0 / g.val.val 3 0)
  have hb : σ b = -b := by
    have hi := column_pairing E σ hσ g2 0 0
    simp [h21, h22, h23, gram] at hi
    have hsd : σ (g.val.val 3 0) ≠ 0 := by simpa using hd
    dsimp [b]
    rw [map_neg, map_div₀]
    field_simp
    linear_combination -hi
  let v := upper E σ hσ 0 b 0 hb (by simp)
  have hv : v ∈ H := hU _ _ _ _ _
  let g3 := v * g2
  have h3 (i : Fin 4) : g3.val.val i 0 = ![0,0,0,g.val.val 3 0] i := by
    change (v.val.val * g2.val.val) i 0 = _
    fin_cases i <;>
      simp [v, upper, upperMatrix, Matrix.mul_apply, Fin.sum_univ_succ, h21, h22, h23, b, hd]
  let w := outerWeyl E σ hσ s hs
  have hw : w ∈ H := outerWeyl_mem E σ hσ H hU _ _
  let g4 := w * g3
  have h4 (i : Fin 4) : g4.val.val i 0 = ![s * g.val.val 3 0,0,0,0] i := by
    change (w.val.val * g3.val.val) i 0 = _
    rw [outerWeyl_val E σ hσ s hs hs0]
    fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, h3]
  let d := levi E σ hσ (SpecialLinearGroup.diag2 ((s * g.val.val 3 0)⁻¹)
    (inv_ne_zero (mul_ne_zero hs0 hd)))
  have hdH : d ∈ H := hL _
  have h5 (i : Fin 4) : (d * g4).val.val i 0 = ![1,0,0,0] i := by
    change (d.val.val * g4.val.val) i 0 = _
    fin_cases i <;>
      simp [d, levi, leviMatrix, SpecialLinearGroup.diag2_coe', Matrix.mul_apply,
        Fin.sum_univ_succ, h4, hs0, hd, mul_assoc]
  have hmem := mem_of_fixed_point E σ hσ H hL hU s hs hs0 (d * g4) h5
  exact (H.mul_mem_cancel_left ht).mp ((H.mul_mem_cancel_left hu).mp
    ((H.mul_mem_cancel_left hv).mp ((H.mul_mem_cancel_left hw).mp
      ((H.mul_mem_cancel_left hdH).mp hmem))))

include hL hU in
/-- Signed unitary elimination over a field with a nonzero skew scalar. -/
theorem eq_top (s : E) (hs : σ s = -s) (hs0 : s ≠ 0) : H = ⊤ := by
  have hlast := mem_of_last_entry E σ hσ H hL hU s hs hs0
  have hp := pair_mem E σ hσ H hL
  have hm := middleWeyl_mem E σ hσ H hU s hs
  have ho := outerWeyl_mem E σ hσ H hU s hs
  apply top_unique
  intro g _
  by_cases h3 : g.val.val 3 0 ≠ 0
  · exact hlast g h3
  by_cases h2 : g.val.val 2 0 ≠ 0
  · apply (H.mul_mem_cancel_left hp).mp
    apply hlast
    change ((pair E σ hσ).val.val * g.val.val) 3 0 ≠ 0
    rw [pair_val]
    simpa [Matrix.mul_apply, Fin.sum_univ_succ] using h2
  by_cases h1 : g.val.val 1 0 ≠ 0
  · apply (H.mul_mem_cancel_left hm).mp
    apply (H.mul_mem_cancel_left hp).mp
    apply hlast
    change ((pair E σ hσ).val.val * ((middleWeyl E σ hσ s hs).val.val * g.val.val)) 3 0 ≠ 0
    rw [pair_val, middleWeyl_val E σ hσ s hs hs0]
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] using
      mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hs0)) h1
  have h0 : g.val.val 0 0 ≠ 0 := by
    intro h0
    apply GeneralLinearGroup.det_ne_zero g.val
    apply Matrix.det_eq_zero_of_column_eq_zero 0
    intro i
    fin_cases i <;> simp_all
  apply (H.mul_mem_cancel_left ho).mp
  apply hlast
  change ((outerWeyl E σ hσ s hs).val.val * g.val.val) 3 0 ≠ 0
  rw [outerWeyl_val E σ hσ s hs hs0]
  simpa [Matrix.mul_apply, Fin.sum_univ_succ] using
    mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hs0)) h0


end Generation

variable (p n : ℕ) [Fact p.Prime] [NeZero n]

/-- The signed plane Levi and radical normally generate the actual SU₄(pⁿ). -/
theorem elementaryNormal_eq_top (hp : p ≠ 2) : elementaryNormal p n = ⊤ := by
  obtain ⟨a, ha, hr, _⟩ := exists_moving_torus (n := n) hp
  have hs0 : a - conjugation p n a ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    exact hr ((div_eq_one_iff_eq (by simpa using ha)).mpr he)
  have hs : conjugation p n (a - conjugation p n a) = -(a - conjugation p n a) := by
    rw [map_sub, conjugation_involutive p n a]
    ring
  exact @Generation.eq_top (Extension p n) inferInstance
    (conjugation p n) (conjugation_involutive p n)
    (elementaryNormal p n) (elementaryNormal_normal p n)
    (fun A => Subgroup.subset_normalClosure (Or.inl ⟨A, rfl⟩))
    (fun z b c hb hc => Subgroup.subset_normalClosure (Or.inr ⟨z, b, c, hb, hc, rfl⟩))
    (a - conjugation p n a) hs hs0

/-- Perfectness includes fixed-field order three; no SL₂(3) perfectness is used. -/
theorem su_isPerfect (hp : p ≠ 2) : Group.IsPerfect (unitaryForm p n).specialSubgroup :=
  su_isPerfect_of_normal_generation p n hp (elementaryNormal_eq_top p n hp)

end ClassicalOrthogonal.Minus.OddSixComparison.Image.Containment
