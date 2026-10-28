module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.NegativeSimple

/-!
# The F₄ Coxeter power as a concrete opposition matrix

The sixth power of the simple Coxeter word acts by minus identity on the
integral Cartan coordinates and sends each root coordinate to its opposite,
up to sign. In characteristic two it is therefore exactly the integral omega
involution. The root calculation uses the third power, a signed permutation
of the four Euclidean coordinates, and then squares it.

Omega commutes with the specialized Tits words and exchanges the two simple
curves. Transport along the canonical root routes thus proves its conjugation
formula for every actual F₄ root curve, including all divided-power terms.

Source: the integral Geck construction and the Weyl representatives in
GLS3, §§2.3.4–2.3.8 and 2.4.8 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
namespace ReeF4.LocalBlockInput.PairNormalization.WeylOpposition

open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Matrix
noncomputable section
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
local notation "s" => typeF4RootPairing_baseEquiv

/-- The simple-node Coxeter word in the fixed F₄ base. -/
def coxeterWord : List typeF4RootPairing_base.support := [s 0, s 1, s 2, s 3]
private def coxeterMatrix : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex ℤ := titsWord (P := typeF4RootPairing) coxeterWord

private lemma cartan_action (i j : Fin 4) :
    titsLift (P := typeF4RootPairing) (s i) *ᵥ u (s j) = u (s j) - |typeF4CartanMatrix i j| • u (s i) := by
  rw [titsLift_mulVec_u, typeF4RootPairing_base_cartan_apply]

private lemma C_u (j : Fin 4) :
    coxeterMatrix *ᵥ u (s j) =
    ![-u (s 1), -u (s 0) + u (s 1) - u (s 2), -u (s 3), (2 : ℤ) • u (s 0) - (2 : ℤ) • u (s 1) + u (s 2) - u (s 3)] j := by
  fin_cases j <;>
    simp only [coxeterMatrix, coxeterWord, titsWord, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_sub, Matrix.mulVec_smul, cartan_action]
  all_goals norm_num [typeF4CartanMatrix, Matrix.cons_val, Fin.reduceFinMk, Fin.ext_iff]
  all_goals try simp only [show (⟨2, by decide⟩ : Fin 4) = 2 from rfl,
    show (⟨3, by decide⟩ : Fin 4) = 3 from rfl]
  all_goals ring

private lemma simple_reflection_val (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val = r.val -
      ((if i.val < 2 then 1 else 2) * dot r.val (typeF4SimpleRoot i)) •
        typeF4SimpleRoot i := by
  rw [← typeF4RootPairing_root, RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_root, typeF4RootPairing_pairing,
    typeF4CorootScale_simpleRoot]
  rfl

private lemma coxeterWord_root (r : F4Chevalley.Root) :
    (reflectionWord (P := typeF4RootPairing) coxeterWord r).val =
      ![(r.val 0 + r.val 1 + r.val 2 + r.val 3) / 2,
        (-r.val 0 + r.val 1 + r.val 2 - r.val 3) / 2,
        (r.val 0 + r.val 1 - r.val 2 - r.val 3) / 2,
        (r.val 0 - r.val 1 + r.val 2 - r.val 3) / 2] := by
  simp only [coxeterWord, reflectionWord, typeF4RootPairing_baseEquiv_val,
    simple_reflection_val]
  ext k
  fin_cases k <;>
    simp [typeF4SimpleRoot, dot, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail, Fin.reduceFinMk] <;> ring

private lemma C_six_u (j : Fin 4) : coxeterMatrix ^ 6 *ᵥ u (s j) = -u (s j) := by
  have h0 : coxeterMatrix *ᵥ u (s 0) = -u (s 1) := C_u 0
  have h1 : coxeterMatrix *ᵥ u (s 1) = -u (s 0) + u (s 1) - u (s 2) := C_u 1
  have h2 : coxeterMatrix *ᵥ u (s 2) = -u (s 3) := C_u 2
  have h3 : coxeterMatrix *ᵥ u (s 3) = (2 : ℤ) • u (s 0) - (2 : ℤ) • u (s 1) +
      u (s 2) - u (s 3) := C_u 3
  fin_cases j <;>
    simp only [show (⟨2, by decide⟩ : Fin 4) = 2 from rfl,
      show (⟨3, by decide⟩ : Fin 4) = 3 from rfl,
      show (⟨0, by decide⟩ : Fin 4) = 0 from rfl,
      show (⟨1, by decide⟩ : Fin 4) = 1 from rfl,
      pow_succ', pow_zero, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      h0, h1, h2, h3, Matrix.mulVec_sub, Matrix.mulVec_add,
      Matrix.mulVec_neg, Matrix.mulVec_smul]
  all_goals module

private lemma coxeterWord_cube_root (r : F4Chevalley.Root) :
    ((reflectionWord (P := typeF4RootPairing) coxeterWord)^[3] r).val =
      ![r.val 1, -r.val 0, -r.val 3, r.val 2] := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, coxeterWord_root]
  ext k
  fin_cases k <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> ring

private lemma coxeterWord_six_root (r : F4Chevalley.Root) :
    (reflectionWord (P := typeF4RootPairing) coxeterWord)^[6] r = -r := by
  apply Subtype.ext
  have hn : (-r).val = -r.val := by
    change typeF4RootPairing.root (-r) = -typeF4RootPairing.root r
    simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self]
  rw [hn, show 6 = 3 + 3 from rfl, Function.iterate_add_apply]
  simp only [coxeterWord_cube_root]
  ext k
  fin_cases k <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

open ReeF4.WordRelations.Faithfulness.Adjoint
variable {K : Type*} [CommRing K]

private lemma cast_mulVec (A : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex ℤ)
    (v : F4Chevalley.BasisIndex → ℤ) :
    (Int.castRingHom K) ∘ (A *ᵥ v) =
      A.map (Int.castRingHom K) *ᵥ ((Int.castRingHom K) ∘ v) := by
  ext i
  exact (Int.castRingHom K).map_mulVec A v i

private lemma cast_single (j : F4Chevalley.BasisIndex) :
    (Int.castRingHom K) ∘ (Pi.single j (1 : ℤ)) = Pi.single j 1 := by
  classical
  ext i
  simp [Pi.single_apply]

private lemma cast_smul (z : ℤ) (v : F4Chevalley.BasisIndex → ℤ) :
    (Int.castRingHom K) ∘ (z • v) = (z : K) • ((Int.castRingHom K) ∘ v) := by
  ext i
  simp

private lemma cast_neg (v : F4Chevalley.BasisIndex → ℤ) :
    (Int.castRingHom K) ∘ (-v) = -((Int.castRingHom K) ∘ v) := by
  ext i
  simp

variable [CharP K 2]

private lemma cast_wordSign (w : List typeF4RootPairing_base.support) (r : F4Chevalley.Root) :
    (titsWordSign (P := typeF4RootPairing) w r : K) = 1 := by
  induction w with
  | nil => simp [titsWordSign]
  | cons i w ih =>
    simp only [titsWordSign, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
      CharTwo.neg_eq, one_pow, mul_one, ih]

private lemma word_root (w : List typeF4RootPairing_base.support) (r : F4Chevalley.Root) :
    (titsWordUnit (K := K) w : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex K) *ᵥ
      Pi.single (Sum.inr r) 1 =
        Pi.single (Sum.inr (reflectionWord (P := typeF4RootPairing) w r)) 1 := by
  have h := congrArg (fun v : F4Chevalley.BasisIndex → ℤ => (Int.castRingHom K) ∘ v)
    (titsWord_mulVec_v (P := typeF4RootPairing) w r)
  simpa only [cast_mulVec, cast_smul, v, cast_single, titsWordUnit_val,
    cast_wordSign, one_smul] using h

private lemma word_pow_root (w : List typeF4RootPairing_base.support) (n : ℕ)
    (r : F4Chevalley.Root) :
    (titsWordUnit (K := K) w : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex K) ^ n *ᵥ
      Pi.single (Sum.inr r) 1 =
        Pi.single (Sum.inr ((reflectionWord (P := typeF4RootPairing) w)^[n] r)) 1 := by
  induction n with
  | zero => simp only [pow_zero, Matrix.one_mulVec, Function.iterate_zero_apply]
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, word_root, Function.iterate_succ_apply']

private lemma word_six_cartan (j : Fin 4) :
    (titsWordUnit (K := K) coxeterWord : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex K) ^ 6 *ᵥ
      Pi.single (Sum.inl (s j)) 1 = Pi.single (Sum.inl (s j)) 1 := by
  have h := congrArg (fun v : F4Chevalley.BasisIndex → ℤ => (Int.castRingHom K) ∘ v)
    (C_six_u j)
  have hn : -(Pi.single (Sum.inl (s j)) (1 : K) : F4Chevalley.BasisIndex → K) =
      Pi.single (Sum.inl (s j)) 1 := by ext i; exact CharTwo.neg_eq _
  simpa only [cast_mulVec, cast_neg, u, cast_single, coxeterMatrix, Matrix.map_pow,
    titsWordUnit_val, hn] using h

/-- In characteristic two, the sixth Coxeter power is the actual opposition matrix. -/
theorem coxeterWord_pow_six_eq_omega : titsWordUnit (K := K) coxeterWord ^ 6 = omegaUnit := by
  apply Units.ext
  change (titsWordUnit (K := K) coxeterWord : Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex K) ^ 6 = _
  apply Matrix.ext_of_mulVec_single
  rintro (j | r)
  · obtain ⟨j, rfl⟩ := typeF4RootPairing_baseEquiv.surjective j
    rw [word_six_cartan, omegaUnit_mulVec_cartan]
  · rw [word_pow_root, coxeterWord_six_root, omegaUnit_mulVec_root]

/-- The opposition matrix conjugates every canonical root curve to its opposite. -/
theorem omega_conj_rootCurve (r : F4Chevalley.Root) (t : K) :
    omegaUnit * F4Chevalley.rootCurve r t * omegaUnit⁻¹ = F4Chevalley.rootCurve (-r) t := by
  have hp (r : F4Chevalley.Root) (hr : typeF4RootPairing_base.IsPos r) :
      omegaUnit * F4Chevalley.rootCurve r t * omegaUnit⁻¹ = F4Chevalley.rootCurve (-r) t := by
    rw [rootCurve_pos_transport r hr, rootCurve_neg_transport r hr,
      negativeUnit_eq_omega_conjugate]
    have h := (omegaUnit_commute_titsWordUnit (K := K)
      (rootRoute (P := typeF4RootPairing) r).word).eq
    have hi := (omegaUnit_commute_titsWordUnit (K := K)
      (rootRoute (P := typeF4RootPairing) r).word).inv_inv.eq
    calc
      _ = (omegaUnit * titsWordUnit (rootRoute (P := typeF4RootPairing) r).word) *
          RootPairing.SimpleGeckGroup.positiveUnit (rootRoute (P := typeF4RootPairing) r).simple t *
          ((titsWordUnit (rootRoute (P := typeF4RootPairing) r).word)⁻¹ * omegaUnit⁻¹) := by group
      _ = _ := by rw [h, ← hi]; group
  by_cases hr : typeF4RootPairing_base.IsPos r
  · exact hp r hr
  · have h := hp (-r) ((RootPairing.Base.IsPos.neg_iff_not _ _).mpr hr)
    simp only [neg_neg] at h
    rw [← h]
    have ho : (omegaUnit (K := K))⁻¹ = omegaUnit := Units.ext rfl
    simp only [ho]
    have hoo : (omegaUnit (K := K)) * omegaUnit = 1 := Units.ext omegaUnit_mul_self
    simp only [← mul_assoc, hoo, one_mul]
    simp only [mul_assoc, hoo, mul_one]

end
end ReeF4.LocalBlockInput.PairNormalization.WeylOpposition
end
