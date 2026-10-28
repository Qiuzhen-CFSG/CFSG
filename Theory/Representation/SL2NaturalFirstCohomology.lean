module

public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.FirstCohomologyLinearTransport
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# First cohomology of the natural SL₂-module in characteristic two

For a finite field `K` of characteristic two with more than two elements, the
first cohomology of the actual matrix action on `Fin 2 → K` is isomorphic to `K`.
The explicit cocycle sends a matrix with rows `(a,b)` and `(c,d)` to
`(√(ab), √(cd))`, using inverse Frobenius for the square root.

To prove completeness, subtract a principal cocycle to kill one nonidentity
split diagonal element. Commutation kills the whole diagonal subgroup and the
Weyl relation kills the coordinate swap. Squaring an upper transvection forces
the second coordinate of its cocycle value to vanish. Diagonal conjugation then
determines every upper value from the value at parameter one. The swap determines
the lower values, and transvection generation determines the entire cocycle.
The explicit cocycle is not principal because the diagonal subgroup has no
nonzero fixed vector.

Scalar restriction gives dimension `n` over `ZMod 2` when `|K| = 2^n`, `n > 1`.
The center of SL₂ is trivial in characteristic two, so the natural action is
also an honest representation of the usual projective special linear quotient.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*, Lemma
I.1.6(2), printed p.408 (combined manuscript PDF p.419), citing Jones--Parshall,
“On the 1-cohomology of finite groups of Lie type” (1976), pp.313–328. The proof
here is the direct matrix calculation, including the case `|K| = 4`.
-/

open Matrix Matrix.SpecialLinearGroup
open Representation Representation.OneCohomology
open scoped Matrix

namespace Representation.SL2NaturalH1
variable {K : Type*} [Field K] [CharP K 2] [Finite K]
private noncomputable abbrev root : K ≃+* K := (frobeniusEquiv K 2).symm

private abbrev upper (x : K) : SpecialLinearGroup (Fin 2) K := transvection zero_ne_one x
private abbrev lower (x : K) : SpecialLinearGroup (Fin 2) K := transvection one_ne_zero x
private noncomputable abbrev diagonal (x : K) (hx : x ≠ 0) := diag2 x hx

omit [CharP K 2] [Finite K] in
private theorem action_apply (g : SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K) (i : Fin 2) :
    specialLinearNatural 2 g v i = g.val i 0 * v 0 + g.val i 1 * v 1 := by
  simp [specialLinearNatural_apply, mulVec, dotProduct, Fin.sum_univ_two]

private theorem root_sq (x : K) : root (x ^ 2) = x := frobeniusEquiv_symm_pow K 2 x

private theorem sq_root (x : K) : root x ^ 2 = x := frobeniusEquiv_symm_pow_p K 2 x

omit [Finite K] in
private theorem det_relation (g : SpecialLinearGroup (Fin 2) K) :
    g.val 0 0 * g.val 1 1 + g.val 0 1 * g.val 1 0 = 1 := by
  simpa only [det_fin_two, CharTwo.sub_eq_add] using g.property

/-- The square-root cocycle for the natural matrix action. -/
public noncomputable def sqrtCocycle : cocycles (specialLinearNatural (k := K) 2) :=
  ⟨fun g i => root (g.val i 0 * g.val i 1), by
    intro g h
    funext i
    apply CharTwo.sq_injective
    change (root ((g * h).val i 0 * (g * h).val i 1)) ^ 2 =
      (specialLinearNatural 2 g (fun j => root (h.val j 0 * h.val j 1)) i +
        root (g.val i 0 * g.val i 1)) ^ 2
    rw [action_apply]
    simp only [CharTwo.add_sq, mul_pow, sq_root, coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
    calc
      _ = g.val i 0 ^ 2 * (h.val 0 0 * h.val 0 1) +
          g.val i 1 ^ 2 * (h.val 1 0 * h.val 1 1) +
          g.val i 0 * g.val i 1 *
            (h.val 0 0 * h.val 1 1 + h.val 0 1 * h.val 1 0) := by ring
      _ = _ := by rw [det_relation]; ring⟩

/-- Coordinates of the square-root cocycle. -/
public theorem sqrtCocycle_apply (g : SpecialLinearGroup (Fin 2) K) (i : Fin 2) :
    (sqrtCocycle (K := K)).val g i =
      (frobeniusEquiv K 2).symm (g.val i 0 * g.val i 1) := by rfl

private theorem sqrtCocycle_upper (x : K) : (sqrtCocycle (K := K)).val (upper x) = ![root x, 0] := by
  ext i
  fin_cases i <;> simp [sqrtCocycle, upper, transvection_coe]

private theorem sqrtCocycle_diagonal (x : K) (hx : x ≠ 0) :
    (sqrtCocycle (K := K)).val (diagonal x hx) = 0 := by
  ext i
  fin_cases i <;> simp [sqrtCocycle, diagonal, diag2_coe']

omit [CharP K 2] [Finite K] in
private theorem action_upper (x : K) (v : Fin 2 → K) :
    specialLinearNatural 2 (upper x) v = ![v 0 + x * v 1, v 1] := by
  ext i
  fin_cases i <;> simp [action_apply, upper, transvection_coe]

omit [CharP K 2] [Finite K] in
private theorem action_diagonal (x : K) (hx : x ≠ 0) (v : Fin 2 → K) :
    specialLinearNatural 2 (diagonal x hx) v = ![x * v 0, x⁻¹ * v 1] := by
  ext i
  fin_cases i <;> simp [action_apply, diagonal, diag2_coe']

omit [Finite K] in
private def swap : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; 1, 0], by simp [det_fin_two, CharTwo.neg_eq]⟩

omit [Finite K] in
private theorem action_swap (v : Fin 2 → K) :
    specialLinearNatural 2 (swap (K := K)) v = ![v 1, v 0] := by
  ext i
  simp only [action_apply]
  fin_cases i <;> simp [swap]

omit [CharP K 2] [Finite K] in
private theorem diagonal_commute (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    diagonal x hx * diagonal y hy = diagonal y hy * diagonal x hx := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal, diag2_coe', mul_comm]

omit [Finite K] in
private theorem diagonal_swap (x : K) (hx : x ≠ 0) :
    diagonal x hx * swap = swap * diagonal x⁻¹ (inv_ne_zero hx) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> (simp only [coe_mul]; simp [diagonal, diag2_coe', swap, Matrix.mul_apply, Fin.sum_univ_two])

omit [CharP K 2] [Finite K] in
private theorem diagonal_upper (x : K) (hx : x ≠ 0) (y : K) :
    diagonal x hx * upper y = upper (x ^ 2 * y) * diagonal x hx := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_mul, diagonal, diag2_coe', upper, transvection_coe, Matrix.mul_apply, Fin.sum_univ_two, pow_two,
      mul_assoc, hx, mul_comm, mul_left_comm]
  field_simp

omit [Finite K] in
private theorem swap_upper (x : K) : swap * upper x = lower x * swap (K := K) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> (simp only [coe_mul]; simp [swap, upper, lower, transvection_coe, Matrix.mul_apply, Fin.sum_univ_two])

omit [Finite K] in
private theorem upper_square (x : K) : upper x * upper x = 1 := by
  rw [← transvection_add, CharTwo.add_self_eq_zero, transvection_coeff_zero]

omit [CharP K 2] [Finite K] in
private theorem cocycle_mul (f : cocycles (specialLinearNatural (k := K) 2))
    (g h : SpecialLinearGroup (Fin 2) K) :
    f.val (g * h) = specialLinearNatural 2 g (f.val h) + f.val g := f.property g h

omit [CharP K 2] [Finite K] in
private theorem cocycle_one (f : cocycles (specialLinearNatural (k := K) 2)) : f.val 1 = 0 := by
  have h := f.property 1 1
  simpa using h.symm

omit [CharP K 2] [Finite K] in
private theorem diagonal_fixed_eq_zero (x : K) (hx : x ≠ 0) (hx1 : x ≠ 1)
    (v : Fin 2 → K) (hv : specialLinearNatural 2 (diagonal x hx) v = v) : v = 0 := by
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  rw [action_diagonal] at h0 h1
  have hv0 : v 0 = 0 := by
    have : (x - 1) * v 0 = 0 := by simpa [sub_mul] using sub_eq_zero.mpr h0
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hx1)
  have hv1 : v 1 = 0 := by
    have : (x⁻¹ - 1) * v 1 = 0 := by simpa [sub_mul] using sub_eq_zero.mpr h1
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (inv_ne_one.mpr hx1))
  ext i
  fin_cases i <;> assumption


omit [CharP K 2] [Finite K] in
private theorem exists_normalized (a : K) (ha : a ≠ 0) (ha1 : a ≠ 1)
    (f : cocycles (specialLinearNatural (k := K) 2)) :
    ∃ v : Fin 2 → K, (f - principal _ v).val (diagonal a ha) = 0 := by
  let v : Fin 2 → K := ![f.val (diagonal a ha) 0 / (a - 1),
    f.val (diagonal a ha) 1 / (a⁻¹ - 1)]
  refine ⟨v, ?_⟩
  funext i
  change f.val (diagonal a ha) i -
    (specialLinearNatural 2 (diagonal a ha) v i - v i) = 0
  rw [action_diagonal]
  fin_cases i <;> dsimp [v] <;>
    field_simp [sub_ne_zero.mpr ha1, sub_ne_zero.mpr (inv_ne_one.mpr ha1)] <;> ring

omit [CharP K 2] [Finite K] in
private theorem normalized_diagonal (a : K) (ha : a ≠ 0) (ha1 : a ≠ 1)
    (f : cocycles (specialLinearNatural (k := K) 2))
    (hf : f.val (diagonal a ha) = 0) (x : K) (hx : x ≠ 0) :
    f.val (diagonal x hx) = 0 := by
  apply diagonal_fixed_eq_zero a ha ha1
  have h := congrArg f.val (diagonal_commute a x ha hx)
  simpa only [cocycle_mul, hf, map_zero, add_zero, zero_add] using h

omit [Finite K] in
private theorem normalized_swap (a : K) (ha : a ≠ 0) (ha1 : a ≠ 1)
    (f : cocycles (specialLinearNatural (k := K) 2))
    (hf : f.val (diagonal a ha) = 0) : f.val swap = 0 := by
  apply diagonal_fixed_eq_zero a ha ha1
  have h := congrArg f.val (diagonal_swap a ha)
  simpa only [cocycle_mul, hf, normalized_diagonal a ha ha1 f hf,
    map_zero, add_zero, zero_add] using h

omit [Finite K] in
private theorem cocycle_upper_second (f : cocycles (specialLinearNatural (k := K) 2))
    (x : K) : f.val (upper x) 1 = 0 := by
  by_cases hx : x = 0
  · subst x
    simp only [upper, transvection_coeff_zero, cocycle_one, Pi.zero_apply]
  · have h := congrFun (f.property (upper x) (upper x)) 0
    rw [upper_square, cocycle_one, action_upper] at h
    have h' : x * f.val (upper x) 1 = 0 := by
      simpa [add_comm, add_left_comm, CharTwo.add_self_eq_zero, CharTwo.add_cancel_left] using h.symm
    exact (mul_eq_zero.mp h').resolve_left hx

private theorem normalized_upper (a : K) (ha : a ≠ 0) (ha1 : a ≠ 1)
    (f : cocycles (specialLinearNatural (k := K) 2))
    (hf : f.val (diagonal a ha) = 0) (x : K) :
    f.val (upper x) = ![root x * f.val (upper 1) 0, 0] := by
  by_cases hx : x = 0
  · subst x
    simp only [upper, transvection_coeff_zero, cocycle_one, map_zero, zero_mul]
    ext i
    fin_cases i <;> rfl
  · have hs : root x ≠ 0 := (map_ne_zero _).mpr hx
    have h := congrArg f.val (diagonal_upper (root x) hs 1)
    simp only [cocycle_mul, normalized_diagonal a ha ha1 f hf, map_zero,
      add_zero, zero_add, sq_root, mul_one] at h
    rw [← h, action_diagonal, cocycle_upper_second]
    simp

omit [Finite K] in
private theorem normalized_lower (a : K) (ha : a ≠ 0) (ha1 : a ≠ 1)
    (f : cocycles (specialLinearNatural (k := K) 2))
    (hf : f.val (diagonal a ha) = 0) (x : K) :
    f.val (lower x) = ![f.val (upper x) 1, f.val (upper x) 0] := by
  have h := congrArg f.val (swap_upper x)
  simpa only [cocycle_mul, normalized_swap a ha ha1 f hf, map_zero,
    zero_add, add_zero, action_swap] using h.symm

private theorem sqrtCocycle_lower (x : K) : (sqrtCocycle (K := K)).val (lower x) = ![0, root x] := by
  ext i
  fin_cases i <;> simp [sqrtCocycle, lower, transvection_coe]

private theorem normalized_eq (a : K) (ha : a ≠ 0) (ha1 : a ≠ 1)
    (f : cocycles (specialLinearNatural (k := K) 2))
    (hf : f.val (diagonal a ha) = 0) :
    f = f.val (upper 1) 0 • sqrtCocycle := by
  apply Subtype.ext
  funext g
  apply Matrix.SL2.transvection_induction
    (fun g => f.val g = (f.val (upper 1) 0 • sqrtCocycle).val g) ?_ ?_ g
  · intro i j hij x
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change f.val (upper x) = f.val (upper 1) 0 • sqrtCocycle.val (upper x)
      rw [normalized_upper a ha ha1 f hf x, sqrtCocycle_upper]
      ext i
      fin_cases i <;> simp [mul_comm]
    · change f.val (lower x) = f.val (upper 1) 0 • sqrtCocycle.val (lower x)
      rw [normalized_lower a ha ha1 f hf x, normalized_upper a ha ha1 f hf x,
        sqrtCocycle_lower]
      ext i
      fin_cases i <;> simp [mul_comm]
    · exact (hij rfl).elim
  · intro g h hg hh
    rw [f.property, (f.val (upper 1) 0 • sqrtCocycle).property, hg, hh]

private theorem exists_decomposition (a : K) (ha : a ≠ 0) (ha1 : a ≠ 1)
    (f : cocycles (specialLinearNatural (k := K) 2)) :
    ∃ c : K, ∃ v : Fin 2 → K, f = c • sqrtCocycle + principal _ v := by
  obtain ⟨v, hv⟩ := exists_normalized a ha ha1 f
  refine ⟨(f - principal _ v).val (upper 1) 0, v, ?_⟩
  exact sub_eq_iff_eq_add.mp (normalized_eq a ha ha1 _ hv)


private theorem sqrtCocycle_class_ne_zero (a : K) (ha : a ≠ 0) (ha1 : a ≠ 1) :
    classMap (specialLinearNatural (k := K) 2) (sqrtCocycle (K := K)) ≠ 0 := by
  intro h
  obtain ⟨v, hv⟩ := (classMap_eq_zero_iff _ _).mp h
  have hvd := congrArg (fun f : cocycles (specialLinearNatural (k := K) 2) =>
    f.val (diagonal a ha)) hv
  have hfixed : specialLinearNatural 2 (diagonal a ha) v = v := by
    apply sub_eq_zero.mp
    exact hvd.trans (sqrtCocycle_diagonal a ha)
  have hv0 := diagonal_fixed_eq_zero a ha ha1 v hfixed
  subst v
  have h' := congrArg (fun f : cocycles (specialLinearNatural (k := K) 2) =>
    f.val (upper 1) 0) hv
  simp [sqrtCocycle, upper, transvection_coe] at h'

/-- The cohomology class with field parameter `c` is `c` times the square-root class. -/
@[expose] public noncomputable def parameterClass : K →ₗ[K] H1 (specialLinearNatural (k := K) 2) :=
  LinearMap.toSpanSingleton K _ (classMap (specialLinearNatural (k := K) 2) sqrtCocycle)

private theorem parameterClass_bijective_of_parameter (a : K) (ha : a ≠ 0) (ha1 : a ≠ 1) :
    Function.Bijective (parameterClass (K := K)) := by
  constructor
  · exact LinearMap.ker_eq_bot.mp (LinearMap.ker_toSpanSingleton K
      (sqrtCocycle_class_ne_zero a ha ha1))
  · intro z
    obtain ⟨f, rfl⟩ := (principal (specialLinearNatural (k := K) 2)).range.mkQ_surjective z
    obtain ⟨c, v, rfl⟩ := exists_decomposition a ha ha1 f
    refine ⟨c, ?_⟩
    change c • classMap (specialLinearNatural (k := K) 2) sqrtCocycle = classMap (specialLinearNatural (k := K) 2) (c • sqrtCocycle + principal _ v)
    rw [map_add, map_smul,
      (classMap_eq_zero_iff _ _).mpr ⟨v, rfl⟩, add_zero]

omit [CharP K 2] in
private theorem exists_diagonal_parameter (hK : 2 < Nat.card K) :
    ∃ a : K, a ≠ 0 ∧ a ≠ 1 := by
  classical
  let := Fintype.ofFinite K
  have h : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
    simpa [Nat.card_eq_fintype_card] using hK
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card h
  exact ⟨a, by simpa using ha⟩

/-- The classes of scalar multiples of the square-root cocycle parametrize H¹ bijectively. -/
public theorem parameterClass_bijective (hK : 2 < Nat.card K) :
    Function.Bijective (parameterClass (K := K)) := by
  obtain ⟨a, ha, ha1⟩ := exists_diagonal_parameter hK
  exact parameterClass_bijective_of_parameter a ha ha1

/-- Every cohomology class has a unique field parameter. -/
public theorem existsUnique_representative (hK : 2 < Nat.card K)
    (z : H1 (specialLinearNatural (k := K) 2)) :
    ∃! c : K, classMap (specialLinearNatural (k := K) 2) (c • sqrtCocycle) = z := by
  obtain ⟨c, hc⟩ := (parameterClass_bijective hK).surjective z
  refine ⟨c, ?_, ?_⟩
  · simpa only [parameterClass, LinearMap.toSpanSingleton_apply, map_smul] using hc
  · intro d hd
    apply (parameterClass_bijective hK).injective
    have hd' : parameterClass d = z := by
      simpa only [parameterClass, LinearMap.toSpanSingleton_apply, map_smul] using hd
    exact hd'.trans hc.symm

/-- The first cohomology is one copy of the defining field. -/
@[expose] public noncomputable def cohomologyEquiv (hK : 2 < Nat.card K) :
    H1 (specialLinearNatural (k := K) 2) ≃ₗ[K] K :=
  (LinearEquiv.ofBijective parameterClass (parameterClass_bijective hK)).symm

/-- The natural SL₂-module has first-cohomology dimension one over the defining field. -/
public theorem finrank_eq_one (hK : 2 < Nat.card K) :
    Module.finrank K (H1 (specialLinearNatural (k := K) 2)) = 1 := by
  rw [(cohomologyEquiv hK).finrank_eq, Module.finrank_self]

omit [Finite K] in
/-- The center of SL₂ over any characteristic-two field is trivial. -/
public theorem center_eq_bot : Subgroup.center (SpecialLinearGroup (Fin 2) K) = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  obtain ⟨a, ha, hag⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have ha1 : a = 1 := CharTwo.sq_injective (by simpa using ha)
  subst a
  apply Subtype.ext
  simpa using hag.symm

omit [Finite K] in
/-- In characteristic two the usual projective quotient is the special linear group itself. -/
@[expose] public noncomputable def projectiveEquiv :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* SpecialLinearGroup (Fin 2) K :=
  (QuotientGroup.quotientMulEquivOfEq center_eq_bot).trans QuotientGroup.quotientBot

omit [Finite K] in
public theorem projectiveEquiv_mk (g : SpecialLinearGroup (Fin 2) K) :
    projectiveEquiv (QuotientGroup.mk g) = g := rfl

omit [Finite K] in
/-- The natural module for the projective special linear group, through its canonical lift. -/
@[expose] public noncomputable def projectiveNatural :
    Representation K (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) (Fin 2 → K) :=
  (specialLinearNatural 2).comp (projectiveEquiv (K := K)).toMonoidHom

omit [Finite K] in
public theorem projectiveNatural_mk (g : SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K) :
    projectiveNatural (QuotientGroup.mk g) v = specialLinearNatural 2 g v := rfl

public theorem finrank_projective_eq_one (hK : 2 < Nat.card K) :
    Module.finrank K (H1 (projectiveNatural (K := K))) = 1 := by
  let e := H1Congr projectiveNatural (specialLinearNatural 2) projectiveEquiv
    (LinearEquiv.refl K (Fin 2 → K)) (by intros; rfl)
  rw [e.finrank_eq, finrank_eq_one hK]

variable [Algebra (ZMod 2) K]

omit [CharP K 2] in
/-- A field with `2^n` elements has degree `n` over its binary prime field. -/
public theorem field_finrank (n : ℕ) (hK : Nat.card K = 2 ^ n) :
    Module.finrank (ZMod 2) K = n := by
  let := Fintype.ofFinite K
  apply Nat.pow_right_injective (by omega : 2 ≤ 2)
  calc
    2 ^ Module.finrank (ZMod 2) K = Fintype.card K := by
      simpa using (Module.card_eq_pow_finrank (K := ZMod 2) (V := K)).symm
    _ = 2 ^ n := by simpa [Nat.card_eq_fintype_card] using hK

/-- Aschbacher--Smith I.1.6(2), in the special linear matrix model. -/
public theorem finrank_restrict_eq (n : ℕ) (hn : 1 < n) (hK : Nat.card K = 2 ^ n) :
    Module.finrank (ZMod 2)
      (H1 (restrictScalars (k := ZMod 2) (specialLinearNatural (k := K) 2))) = n := by
  have hK' : 2 < Nat.card K := by
    rw [hK]
    exact (show 2 ^ 1 < 2 ^ n from Nat.pow_lt_pow_right (by omega) hn)
  rw [finrank_restrictScalars, finrank_eq_one hK', field_finrank n hK, mul_one]

/-- Aschbacher--Smith I.1.6(2), for the natural module of the projective quotient. -/
public theorem finrank_projective_restrict_eq (n : ℕ) (hn : 1 < n) (hK : Nat.card K = 2 ^ n) :
    Module.finrank (ZMod 2)
      (H1 (restrictScalars (k := ZMod 2) (projectiveNatural (K := K)))) = n := by
  have hK' : 2 < Nat.card K := by
    rw [hK]
    exact (show 2 ^ 1 < 2 ^ n from Nat.pow_lt_pow_right (by omega) hn)
  rw [finrank_restrictScalars, finrank_projective_eq_one hK', field_finrank n hK, mul_one]

end Representation.SL2NaturalH1
