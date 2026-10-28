module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootTorus.Coordinates
/-!
# A vacuum and diagonal elements in the four-plane Clifford algebra

Write `eᵢ` and `fᵢ` for the two isotropic coordinate vectors, `Pᵢ = eᵢfᵢ`
and `Qᵢ = fᵢeᵢ = 1 - Pᵢ`. The product of the four `Qᵢ` is nonzero:
if it vanished, the relations `eᵢ² = fᵢ² = 0` and `Pᵢ + Qᵢ = 1`
would successively remove all four factors and force `1 = 0`.

For the published ordinary diagonal `d`, the element
`t₃ • ∏ᵢ (Qᵢ + dᵢ • Pᵢ)` acts on this vacuum by `t₃`. Its norm is one
and it intertwines Clifford vectors with their ordinary diagonal action.
The ratio with the actual coroot parameter is therefore an even element
centralizing every vector. The split Clifford centralizer theorem makes
it scalar; norm one and characteristic two make that scalar one. This
identifies the explicit element with the genuine Spin coroot product.

Source motivation: GLS3, Theorem 1.12.5(b) and §§1.14.1–2,
`refs/KGroup/GLS3/Chapter1.tex`. This is a concrete Clifford calculation,
independent of a simply connected or fundamental-weight assertion.
-/

@[expose] public section
open Theory.AlgebraicGroup CliffordAlgebra
noncomputable section
namespace Triality.SimplyConnected.Pinning.CorootTorus.SpinClifford
universe u
variable (k : Type u) [Field k]
/-- The Clifford algebra of the fixed four hyperbolic planes. -/
abbrev C := CliffordAlgebra (quadraticForm k)
/-- First isotropic vector of a hyperbolic plane. -/
def e (i : Fin 4) : C k := ι (quadraticForm k) (Pi.single i 1, 0)
/-- Second isotropic vector of a hyperbolic plane. -/
def f (i : Fin 4) : C k := ι (quadraticForm k) (0, Pi.single i 1)
/-- The first hyperbolic projector. -/
def p (i : Fin 4) : C k := e k i * f k i
/-- The complementary hyperbolic projector. -/
def q (i : Fin 4) : C k := f k i * e k i
/-- A diagonal Clifford factor. -/
def factor (i : Fin 4) (a : k) : C k := q k i + a • p k i
/-- The nonzero vector selected by all four complementary projectors. -/
def vacuum : C k := q k 0 * (q k 1 * (q k 2 * q k 3))
@[simp] theorem e_sq (i : Fin 4) : e k i * e k i = 0 := by
  simp [e, ι_sq_scalar]
@[simp] theorem f_sq (i : Fin 4) : f k i * f k i = 0 := by
  simp [f, ι_sq_scalar]
theorem p_add_q (i : Fin 4) : p k i + q k i = 1 := by
  unfold p q e f
  rw [ι_mul_ι_add_swap]
  change algebraMap k (C k) ((hyperbolicForm 4).polarBilin _ _) = 1
  rw [hyperbolicForm_polar]
  simp [Pi.single_apply]
theorem efe (i : Fin 4) : e k i * f k i * e k i = e k i := by
  have h := congrArg (e k i * ·) (p_add_q k i)
  simpa [p, q, mul_add, ← mul_assoc] using h
@[simp] theorem p_sq (i : Fin 4) : p k i * p k i = p k i := by
  simp only [p, ← mul_assoc, efe]
@[simp] theorem q_sq (i : Fin 4) : q k i * q k i = q k i := by
  unfold q
  rw [mul_assoc, ← mul_assoc (e k i), efe]
@[simp] theorem p_mul_q (i : Fin 4) : p k i * q k i = 0 := by
  simp [p, q, mul_assoc, ← mul_assoc (f k i)]
@[simp] theorem q_mul_p (i : Fin 4) : q k i * p k i = 0 := by
  simp [p, q, mul_assoc, ← mul_assoc (e k i)]
@[simp] theorem factor_mul_q (i : Fin 4) (a : k) : factor k i a * q k i = q k i := by
  simp [factor, add_mul]

@[simp] theorem star_p (i : Fin 4) : star (p k i) = q k i := by
  simp [p, q, e, f]
@[simp] theorem star_q (i : Fin 4) : star (q k i) = p k i := by
  simp [p, q, e, f]
@[simp] theorem star_factor_mul (i : Fin 4) (a : k) :
    star (factor k i a) * factor k i a = a • (1 : C k) := by
  simp only [factor, star_add, CliffordAlgebra.star_smul, star_p, star_q,
    add_mul, mul_add, smul_mul_assoc, mul_smul_comm, p_mul_q, q_mul_p,
    p_sq, q_sq, smul_zero, zero_add, add_zero, ← smul_add]
  rw [add_comm, p_add_q]

theorem factor_even (i : Fin 4) (a : k) : factor k i a ∈ even (quadraticForm k) := by
  apply (even (quadraticForm k)).add_mem
  · exact ι_mul_ι_mem_evenOdd_zero _ _ _
  · exact Submodule.smul_mem (even (quadraticForm k)).toSubmodule a
      (ι_mul_ι_mem_evenOdd_zero _ _ _)

private theorem norm_mul (x y : C k) (a b : k)
    (hx : star x * x = a • (1 : C k))
    (hy : star y * y = b • (1 : C k)) :
    star (x * y) * (x * y) = (a * b) • (1 : C k) := by
  calc
    _ = star y * (star x * x) * y := by simp only [star_mul, mul_assoc]
    _ = _ := by rw [hx, mul_smul_comm, mul_one, smul_mul_assoc, hy, smul_smul]

variable [CharP k 2]
private theorem commute_ι_of_polar_zero (v w : QuadraticSpace k)
    (h : (quadraticForm k).polarBilin v w = 0) :
    Commute (ι (quadraticForm k) v) (ι (quadraticForm k) w) := by
  change _ * _ = _ * _
  rw [ι_mul_ι_comm]
  change algebraMap k (C k) ((quadraticForm k).polarBilin v w) - _ = _
  rw [h, map_zero, zero_sub]
  rw [← neg_one_smul k, CharTwo.neg_eq (1 : k), one_smul]
theorem e_commute_e (i j : Fin 4) : Commute (e k i) (e k j) := by
  apply commute_ι_of_polar_zero
  rw [hyperbolicForm_polar]
  simp
theorem f_commute_f (i j : Fin 4) : Commute (f k i) (f k j) := by
  apply commute_ι_of_polar_zero
  rw [hyperbolicForm_polar]
  simp
theorem e_commute_f (i j : Fin 4) (h : i ≠ j) : Commute (e k i) (f k j) := by
  apply commute_ι_of_polar_zero
  rw [hyperbolicForm_polar]
  simp [Pi.single_apply, h.symm]
theorem e_commute_q (i j : Fin 4) (h : i ≠ j) : Commute (e k i) (q k j) :=
  (e_commute_f k i j h).mul_right (e_commute_e k i j)
theorem f_commute_q (i j : Fin 4) (h : i ≠ j) : Commute (f k i) (q k j) :=
  (f_commute_f k i j).mul_right (e_commute_f k j i (Ne.symm h)).symm

omit [CharP k 2] in
private theorem eq_zero_of_q_mul_eq_zero (i : Fin 4) (x : C k)
    (hc : Commute (f k i) x) (h : q k i * x = 0) : x = 0 := by
  have hp : p k i * x = 0 := by
    have hh := congrArg (fun z => e k i * z * f k i) h
    have he : e k i * (q k i * x) * f k i = p k i * x := by
      calc
        _ = (e k i * f k i * e k i) * (x * f k i) := by simp only [q, mul_assoc]
        _ = e k i * (f k i * x) := by rw [efe, hc.eq]
        _ = _ := by rw [p, mul_assoc]
    simpa only [he, mul_zero, zero_mul] using hh
  have hh := congrArg (· * x) (p_add_q k i)
  simpa [add_mul, hp, h] using hh.symm

/-- The vacuum is nonzero, without expanding a PBW basis. -/
theorem vacuum_ne_zero : vacuum k ≠ 0 := by
  intro h
  have h0 := eq_zero_of_q_mul_eq_zero k 0 _
    ((f_commute_q k 0 1 (by decide)).mul_right
      ((f_commute_q k 0 2 (by decide)).mul_right (f_commute_q k 0 3 (by decide)))) h
  have h1 := eq_zero_of_q_mul_eq_zero k 1 _
    ((f_commute_q k 1 2 (by decide)).mul_right (f_commute_q k 1 3 (by decide))) h0
  have h2 := eq_zero_of_q_mul_eq_zero k 2 _ (f_commute_q k 2 3 (by decide)) h1
  have h3 := eq_zero_of_q_mul_eq_zero k 3 1 (Commute.one_right _) (by simpa using h2)
  let : Nontrivial (C k) := (standardHyperbolicSplit (k := k) 4).cliffordToExterior.symm.injective.nontrivial
  exact one_ne_zero h3
theorem factor_commute_q (i j : Fin 4) (h : i ≠ j) (a : k) :
    Commute (factor k i a) (q k j) :=
  ((f_commute_q k i j h).mul_left (e_commute_q k i j h)).add_left
    (((e_commute_q k i j h).mul_left (f_commute_q k i j h)).smul_left a)

theorem factor_mul_vacuum (i : Fin 4) (a : k) :
    factor k i a * vacuum k = vacuum k := by
  fin_cases i
  · change factor k 0 a * vacuum k = vacuum k
    rw [vacuum, ← mul_assoc, factor_mul_q]
  · change factor k 1 a * vacuum k = vacuum k
    rw [vacuum, (factor_commute_q k 1 0 (by decide) a).left_comm,
      ← mul_assoc (factor k 1 a), factor_mul_q]
  · change factor k 2 a * vacuum k = vacuum k
    rw [vacuum, (factor_commute_q k 2 0 (by decide) a).left_comm,
      (factor_commute_q k 2 1 (by decide) a).left_comm,
      ← mul_assoc (factor k 2 a), factor_mul_q]
  · change factor k 3 a * vacuum k = vacuum k
    rw [vacuum, (factor_commute_q k 3 0 (by decide) a).left_comm,
      (factor_commute_q k 3 1 (by decide) a).left_comm,
      (factor_commute_q k 3 2 (by decide) a).left_comm, factor_mul_q]

omit [CharP k 2] in
/-- Explicit Clifford element for the ordered simple-coroot parameter. -/
def diagonalElement (t : Fin 4 → kˣ) : C k :=
  (t 3 : k) • (factor k 0 (diagonal k t 0) *
    (factor k 1 (diagonal k t 1) *
      (factor k 2 (diagonal k t 2) * factor k 3 (diagonal k t 3))))

/-- The explicit element has vacuum eigenvalue equal to the fourth parameter. -/
theorem diagonalElement_mul_vacuum (t : Fin 4 → kˣ) :
    diagonalElement k t * vacuum k = (t 3 : k) • vacuum k := by
  simp only [diagonalElement, smul_mul_assoc, mul_assoc, factor_mul_vacuum]

omit [CharP k 2] in
theorem diagonalElement_even (t : Fin 4 → kˣ) :
    diagonalElement k t ∈ even (quadraticForm k) :=
  Submodule.smul_mem (even (quadraticForm k)).toSubmodule _
    ((even (quadraticForm k)).mul_mem (factor_even k _ _)
      ((even (quadraticForm k)).mul_mem (factor_even k _ _)
        ((even (quadraticForm k)).mul_mem (factor_even k _ _) (factor_even k _ _))))

omit [CharP k 2] in
theorem diagonalElement_norm (t : Fin 4 → kˣ) :
    star (diagonalElement k t) * diagonalElement k t = 1 := by
  have hn := norm_mul k _ _ _ _ (star_factor_mul k 0 (diagonal k t 0))
    (norm_mul k _ _ _ _ (star_factor_mul k 1 (diagonal k t 1))
      (norm_mul k _ _ _ _ (star_factor_mul k 2 (diagonal k t 2))
        (star_factor_mul k 3 (diagonal k t 3))))
  unfold diagonalElement
  rw [CliffordAlgebra.star_smul, smul_mul_assoc, mul_smul_comm, hn,
    smul_smul, smul_smul]
  have hs : (t 3 : k) * ((t 3 : k) * ((diagonal k t 0 : k) *
      ((diagonal k t 1 : k) * ((diagonal k t 2 : k) * (diagonal k t 3 : k))))) = 1 := by
    simp [diagonal, mul_comm, mul_left_comm, mul_assoc]
  rw [mul_assoc (t 3 : k), hs, one_smul]


theorem factor_mul_e (i j : Fin 4) (a : kˣ) :
    factor k i (a : k) * e k j =
      (if i = j then (a : k) else 1) • (e k j * factor k i (a : k)) := by
  by_cases h : i = j
  · subst j
    simp only [factor, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
    have hqe : q k i * e k i = 0 := by simp [q, mul_assoc]
    have hep : e k i * p k i = 0 := by simp [p, ← mul_assoc]
    have hpe : p k i * e k i = e k i := efe k i
    have heq : e k i * q k i = e k i := by rw [q, ← mul_assoc, efe]
    rw [hqe, hep, hpe, heq]
    simp
  · rw [if_neg h, one_smul]
    exact (((e_commute_f k j i (Ne.symm h)).symm.mul_left
      (e_commute_e k i j)).add_left
      (((e_commute_e k i j).mul_left (e_commute_f k j i (Ne.symm h)).symm).smul_left _)).eq

theorem factor_mul_f (i j : Fin 4) (a : kˣ) :
    factor k i (a : k) * f k j =
      (if i = j then ((a⁻¹ : kˣ) : k) else 1) • (f k j * factor k i (a : k)) := by
  by_cases h : i = j
  · subst j
    have hfe : f k i * e k i * f k i = f k i := by
      have hh := congrArg (· * f k i) (p_add_q k i)
      simpa [p, q, add_mul, mul_assoc] using hh
    have hpf : p k i * f k i = 0 := by simp [p, mul_assoc]
    have hfq : f k i * q k i = 0 := by simp [q, ← mul_assoc]
    have hqf : q k i * f k i = f k i := hfe
    have hfp : f k i * p k i = f k i := by rw [p, ← mul_assoc, hfe]
    simp only [factor, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
    rw [hpf, hfq, hqf, hfp]
    simp [smul_smul]
  · rw [if_neg h, one_smul]
    exact (((f_commute_f k i j).mul_left
      (e_commute_f k i j h)).add_left
      (((e_commute_f k i j h).mul_left (f_commute_f k i j)).smul_left _)).eq

omit [CharP k 2] in
private theorem mul_intertwine (x y z : C k) (a b : k)
    (hx : x * z = a • (z * x)) (hy : y * z = b • (z * y)) :
    (x * y) * z = (a * b) • (z * (x * y)) := by
  rw [mul_assoc, hy, mul_smul_comm, ← mul_assoc x, hx, smul_mul_assoc,
    smul_smul, mul_comm b a, mul_assoc]

theorem diagonalElement_mul_e (t : Fin 4 → kˣ) (j : Fin 4) :
    diagonalElement k t * e k j = (diagonal k t j : k) • (e k j * diagonalElement k t) := by
  have h := mul_intertwine k _ _ _ _ _ (factor_mul_e k 0 j (diagonal k t 0))
    (mul_intertwine k _ _ _ _ _ (factor_mul_e k 1 j (diagonal k t 1))
      (mul_intertwine k _ _ _ _ _ (factor_mul_e k 2 j (diagonal k t 2))
        (factor_mul_e k 3 j (diagonal k t 3))))
  unfold diagonalElement
  rw [smul_mul_assoc, h, mul_smul_comm, smul_smul, smul_smul]
  congr 1
  fin_cases j <;> norm_num [Fin.ext_iff, mul_comm] <;> rfl

theorem diagonalElement_mul_f (t : Fin 4 → kˣ) (j : Fin 4) :
    diagonalElement k t * f k j = (((diagonal k t j)⁻¹ : kˣ) : k) • (f k j * diagonalElement k t) := by
  have h := mul_intertwine k _ _ _ _ _ (factor_mul_f k 0 j (diagonal k t 0))
    (mul_intertwine k _ _ _ _ _ (factor_mul_f k 1 j (diagonal k t 1))
      (mul_intertwine k _ _ _ _ _ (factor_mul_f k 2 j (diagonal k t 2))
        (factor_mul_f k 3 j (diagonal k t 3))))
  change _ = (((diagonal k t j)⁻¹ : kˣ) : k) • _
  unfold diagonalElement
  rw [smul_mul_assoc, h, mul_smul_comm, smul_smul, smul_smul]
  congr 1
  fin_cases j <;> norm_num [Fin.ext_iff, mul_comm] <;> rfl

omit [CharP k 2] in
theorem vector_expansion (v : QuadraticSpace k) :
    ι (quadraticForm k) v = (∑ i, v.1 i • e k i) + ∑ i, v.2 i • f k i := by
  have hv : v = (∑ i : Fin 4, v.1 i • (Pi.single i 1, (0 : Fin 4 → k))) +
      ∑ i : Fin 4, v.2 i • ((0 : Fin 4 → k), Pi.single i 1) := by
    apply Prod.ext <;> funext j <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_add, map_sum, map_smul, e, f]

theorem diagonalElement_intertwine (t : Fin 4 → kˣ) (v : QuadraticSpace k) :
    diagonalElement k t * ι (quadraticForm k) v =
      ι (quadraticForm k) ((hyperbolicDiagonalPoint 4 (diagonal k t)).1 v) *
        diagonalElement k t := by
  simp only [vector_expansion, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul,
    mul_smul_comm, smul_mul_assoc, diagonalElement_mul_e, diagonalElement_mul_f]
  change (∑ i, v.1 i • ((diagonal k t i : k) • (e k i * diagonalElement k t))) +
      (∑ i, v.2 i • ((((diagonal k t i)⁻¹ : kˣ) : k) • (f k i * diagonalElement k t))) =
    (∑ i, ((diagonal k t i : k) * v.1 i) • (e k i * diagonalElement k t)) +
      ∑ i, ((((diagonal k t i)⁻¹ : kˣ) : k) * v.2 i) • (f k i * diagonalElement k t)
  simp only [smul_smul, mul_comm]


variable [IsAlgClosed k]
/-- The explicit norm-one even Clifford element is the published coroot word. -/
theorem diagonalElement_parameter (t : Fin 4 → kˣ) :
    diagonalElement k t = (pointEquiv k (parameter k t) : C k) := by
  let g : spinGroup (quadraticForm k) := pointEquiv k (parameter k t)
  let x : C k := (g⁻¹ : spinGroup (quadraticForm k)) * diagonalElement k t
  have hgleft : ((g⁻¹ : spinGroup (quadraticForm k)) : C k) * (g : C k) = 1 :=
    spinGroup.coe_star_mul_self g
  have hgright : (g : C k) * ((g⁻¹ : spinGroup (quadraticForm k)) : C k) = 1 :=
    spinGroup.coe_mul_star_self g
  have heven : x ∈ even (quadraticForm k) :=
    (even (quadraticForm k)).mul_mem (spinGroup.mem_even (g⁻¹).property)
      (diagonalElement_even k t)
  have hcomm (v : QuadraticSpace k) : Commute x (ι (quadraticForm k) v) := by
    have hg := naturalAction_clifford k (parameter k t) v
    rw [naturalAction_parameter] at hg
    change ι (quadraticForm k) ((hyperbolicDiagonalPoint 4 (diagonal k t)).1 v) =
      (g : C k) * ι (quadraticForm k) v *
        ((g⁻¹ : spinGroup (quadraticForm k)) : C k) at hg
    change x * ι (quadraticForm k) v = ι (quadraticForm k) v * x
    dsimp only [x]
    rw [mul_assoc, diagonalElement_intertwine, hg]
    simp only [← mul_assoc, hgleft, one_mul]
  obtain ⟨a, ha⟩ := CliffordAlgebra.eq_algebraMap_of_mem_even_of_commute_ι
    (standardHyperbolicSplit (k := k) 4) x heven hcomm
  have hn : star x * x = 1 := by
    change star (((g⁻¹ : spinGroup (quadraticForm k)) : C k) * diagonalElement k t) *
      (((g⁻¹ : spinGroup (quadraticForm k)) : C k) * diagonalElement k t) = 1
    rw [star_mul]
    have hstar : star (((g⁻¹ : spinGroup (quadraticForm k)) : C k)) = (g : C k) :=
      star_star (g : C k)
    rw [hstar]
    calc
      _ = star (diagonalElement k t) *
          ((g : C k) * ((g⁻¹ : spinGroup (quadraticForm k)) : C k)) *
            diagonalElement k t := by simp only [mul_assoc]
      _ = 1 := by rw [hgright, mul_one, diagonalElement_norm]
  let : Nontrivial (C k) :=
    (standardHyperbolicSplit (k := k) 4).cliffordToExterior.symm.injective.nontrivial
  have haa : a * a = 1 := by
    apply FaithfulSMul.algebraMap_injective k (C k)
    rw [ha] at hn
    simpa using hn
  have ha1 : a = 1 := CharTwo.sq_injective (by simpa [pow_two] using haa)
  have hx : x = 1 := by simpa [ha1] using ha
  have hm := congrArg ((g : C k) * ·) hx
  change (g : C k) * (((g⁻¹ : spinGroup (quadraticForm k)) : C k) * diagonalElement k t) =
    (g : C k) * 1 at hm
  simpa only [← mul_assoc, hgright, one_mul, mul_one] using hm

end Triality.SimplyConnected.Pinning.CorootTorus.SpinClifford
