module

public import Theory.SpecificGroups.PSL3.UniversalProjection.Faithfulness.Setup
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Multiplicativity of finite-field torus words

Central defects and cyclicity of the finite field's unit group first imply that
all torus words on a fixed root commute. The square-scaling conjugation formula
then proves multiplicativity whenever either parameter is a square. A direct
root-word calculation proves it when the parameters sum to one. Finally, two
nonsquares summing to one represent the only remaining pair of square classes.

For the finite-field existence argument, if squares were closed under addition,
finiteness would force the additive inverse of one to be a square. Polarization
would then make every element a square in odd characteristic, a contradiction.
Choose squares `a, b` with nonsquare sum `c`; the required pair is `a/c, b/c`.
No matrix faithfulness, Bruhat reduction, or universality theorem is used.

Source: Steinberg, *Lectures on Chevalley Groups* (1968), §6, Lemmas 39–40 and
Theorem 9, printed pp.72–74 (`refs/KGroup/GLS3/Chapter2St1.tex`). The end of
Lemma 40 is taken from the original PDF, since the TeX transcription omits it.
The exported result discharges the torus premise of
`kernelTorusReduction_of_torusMultiplicative` in the independent Bruhat argument.
-/

@[expose] public section

namespace Matrix.PSL3.UniversalProjection.Faithfulness.FiniteTorus
variable {F : Type*} [Field F] [Finite F]

-- Squares cannot form an additive subgroup: otherwise polarization makes every element a square.
private lemma exists_squares_nonsquare_sum (hF : ringChar F ≠ 2) :
    ∃ a b : F, IsSquare a ∧ IsSquare b ∧ ¬IsSquare (a + b) := by
  classical
  by_contra! hc
  have hadd : ∀ a b : F, IsSquare a → IsSquare b → IsSquare (a + b) := hc
  let f : {a : F // IsSquare a} → {a : F // IsSquare a} :=
    fun a => ⟨a.val + 1, hadd _ _ a.property IsSquare.one⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact add_right_cancel (congrArg Subtype.val hab)
  obtain ⟨a, ha⟩ := (Finite.surjective_of_injective hf) ⟨0, IsSquare.zero⟩
  have hneg : IsSquare (-1 : F) := by
    have he : a.val + 1 = 0 := congrArg Subtype.val ha
    have he' : a.val = -1 := eq_neg_of_add_eq_zero_left he
    exact he' ▸ a.property
  obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare hF
  apply hc
  have htwo : (2 : F) ≠ 0 := by
    exact Ring.two_ne_zero hF
  have he : c = ((c + 1) / 2) ^ 2 + (-1) * ((c - 1) / 2) ^ 2 := by
    field_simp
    ring
  rw [he]
  exact hadd _ _ (IsSquare.sq _) (hneg.mul (IsSquare.sq _))

private lemma exists_nonsquares_add_one (hF : ringChar F ≠ 2) :
    ∃ a b : F, ¬IsSquare a ∧ ¬IsSquare b ∧ a + b = 1 := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_squares_nonsquare_sum hF
  have ha0 : a ≠ 0 := by rintro rfl; exact hab (by simpa using hb)
  have hb0 : b ≠ 0 := by rintro rfl; exact hab (by simpa using ha)
  have hc0 : a + b ≠ 0 := by intro hc; exact hab (hc.symm ▸ IsSquare.zero)
  refine ⟨a / (a + b), b / (a + b), ?_, ?_, ?_⟩
  · intro h
    apply hab
    have he : a / (a / (a + b)) = a + b := by field_simp
    exact he ▸ ha.div h
  · intro h
    apply hab
    have he : b / (b / (a + b)) = a + b := by field_simp
    exact he ▸ hb.div h
  · rw [← add_div, div_self hc0]

private lemma square_of_nonsquare_ratio {a b : F} (ha : ¬IsSquare a) (hb : ¬IsSquare b) :
    IsSquare (a / b) := by
  classical
  let := Fintype.ofFinite F
  have ha0 : a ≠ 0 := fun h => ha (h.symm ▸ IsSquare.zero)
  have hb0 : b ≠ 0 := fun h => hb (h.symm ▸ IsSquare.zero)
  apply (quadraticChar_one_iff_isSquare (div_ne_zero ha0 hb0)).mp
  have h1 := quadraticChar_neg_one_iff_not_isSquare.mpr ha
  have h2 := quadraticChar_neg_one_iff_not_isSquare.mpr hb
  have he : quadraticChar F ((a / b) * b) = quadraticChar F (a / b) * quadraticChar F b :=
    map_mul (quadraticChar F) (a / b) b
  rw [div_mul_cancel₀ _ hb0, h1, h2] at he
  linarith

omit [Finite F] in
private lemma unit_isSquare_iff (a : Fˣ) : IsSquare a ↔ IsSquare (a : F) := by
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, rfl⟩
  · rintro ⟨b, hb⟩
    have hb0 : b ≠ 0 := by
      intro h
      simp [h] at hb
    exact ⟨Units.mk0 b hb0, Units.ext hb⟩
end Matrix.PSL3.UniversalProjection.Faithfulness.FiniteTorus

open Theory.SpecificGroups.LinearHigher SteinbergWords
namespace Matrix.PSL3.UniversalProjection.Faithfulness
variable {F : Type*} [Field F]
variable (i j : Fin 3) (hij : i ≠ j)
local notation "h" => torus (F := F) i j hij
local notation "w" => weylWord (generator (F := F)) i j hij
local notation "x" => generator (F := F) (root i j hij)
local notation "y" => generator (F := F) (root j i hij.symm)

private lemma weyl_alternate (t : Fˣ) :
    w t = y (-((t⁻¹ : Fˣ) : F)) * x t * y (-((t⁻¹ : Fˣ) : F)) := by
  have he := weylWord_conj_root generator_relations (by decide : 2 < 3) i j hij t (t : F)
  have hc : -((t⁻¹ : Fˣ) : F) * (t : F) * ((t⁻¹ : Fˣ) : F) =
      -((t⁻¹ : Fˣ) : F) := by simp
  rw [hc, MulAut.conj_apply] at he
  have he' := mul_inv_eq_iff_eq_mul.mp he
  apply mul_right_cancel (b := x (t : F))
  simpa only [weylWord, mul_assoc] using he'

private lemma torus_conj_weyl (s t : Fˣ) :
    MulAut.conj (h s) (w t) = w (t * s ^ 2) := by
  simp only [weylWord, map_mul]
  rw [torusWord_conj_root generator_relations (by decide),
    torusWord_conj_opposite_root generator_relations (by decide)]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, _root_.mul_inv_rev, Units.val_inv_eq_inv_val]
  congr 2 <;> ring

private lemma torus_conj_torus (s t : Fˣ) :
    MulAut.conj (h s) (h t) = h (t * s ^ 2) * (h (s ^ 2))⁻¹ := by
  change MulAut.conj (h s) (w t * w (-1)) = (w _ * w (-1)) * (w _ * w (-1))⁻¹
  rw [map_mul, torus_conj_weyl, torus_conj_weyl]
  simp only [_root_.mul_inv_rev, mul_assoc, mul_inv_cancel_left]
  rw [weylWord_inv generator_relations]
  simp only [neg_mul, one_mul]

private lemma conj_torus_hom : ∃ φ : Fˣ →* MulAut (SteinbergGroup 3 F),
    ∀ s, φ s = MulAut.conj (h s) := by
  refine ⟨{ toFun := fun s => MulAut.conj (h s), map_one' := ?_, map_mul' := ?_ }, fun _ => rfl⟩
  · simp [torus, torusWord_one generator_relations]
  · intro s t
    have hc := torus_defect_mem_center i j hij s t
    have hc' : MulAut.conj (h s * h t * (h (s * t))⁻¹) = 1 := by
      ext g
      rw [MulAut.conj_apply]
      rw [← (Subgroup.mem_center_iff.mp hc g), mul_assoc, mul_inv_cancel, mul_one]
      rfl
    symm
    simpa only [map_mul, map_inv, mul_inv_eq_one] using hc'

-- Lemma 39(b): cyclicity and central defects make the rank-one torus commutative.
private lemma torus_commute [Finite F] (s t : Fˣ) : Commute (h s) (h t) := by
  obtain ⟨φ, hφ⟩ := conj_torus_hom (F := F) i j hij
  obtain ⟨v, hv⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨m, hm⟩ := hv s
  obtain ⟨n, hn⟩ := hv t
  have he (k : ℤ) : MulAut.conj (h (v ^ k)) = MulAut.conj (h v ^ k) := by
    rw [← hφ, map_zpow, hφ, map_zpow]
  have hc (k : ℤ) : Commute (h (v ^ k)) (h v) := by
    have he' := congrArg (fun f : MulAut (SteinbergGroup 3 F) => f (h v)) (he k)
    simp only [MulAut.conj_apply] at he'
    rw [(Commute.refl (h v)).zpow_left k |>.eq] at he'
    simp only [mul_inv_cancel_right] at he'
    exact mul_inv_eq_iff_eq_mul.mp he'
  rw [← hm, ← hn]
  have he' := congrArg (fun f : MulAut (SteinbergGroup 3 F) => f (h (v ^ m))) (he n)
  simp only [MulAut.conj_apply] at he'
  rw [((hc m).symm.zpow_left n).eq] at he'
  simp only [mul_inv_cancel_right] at he'
  exact (show Commute (h (v ^ n)) (h (v ^ m)) from mul_inv_eq_iff_eq_mul.mp he').symm

-- Lemma 39(c), after commuting the two torus words.
private lemma torus_mul_square [Finite F] (s t : Fˣ) : h s * h (t ^ 2) = h (s * t ^ 2) := by
  have he := torus_conj_torus i j hij t s
  rw [MulAut.conj_apply, (torus_commute i j hij t s).eq,
    mul_assoc, mul_inv_cancel, mul_one] at he
  exact (eq_mul_inv_iff_mul_eq.mp he)

private lemma root_mul_weyl (t : Fˣ) (a : F) :
    x a * w t = w t * y (-((t⁻¹ : Fˣ) : F) * a * ((t⁻¹ : Fˣ) : F)) := by
  have he := weylWord_conj_root generator_relations (by decide : 2 < 3) i j hij (-t) a
  simp only [Units.val_inv_eq_inv_val, Units.val_neg, inv_neg, neg_neg, mul_neg] at he
  rw [← weylWord_inv generator_relations, MulAut.conj_apply, inv_inv] at he
  calc
    x a * w t = w t * ((w t)⁻¹ * x a * w t) := by group
    _ = _ := by
      rw [he]
      simp only [Units.val_inv_eq_inv_val, neg_mul]

private lemma opposite_mul_weyl (t : Fˣ) (a : F) :
    y a * w t = w t * x (-(t : F) * a * (t : F)) := by
  have he := weylWord_conj_opposite_root generator_relations (by decide : 2 < 3) i j hij (-t) a
  simp only [Units.val_neg, neg_neg, mul_neg] at he
  rw [← weylWord_inv generator_relations, MulAut.conj_apply, inv_inv] at he
  calc
    y a * w t = w t * ((w t)⁻¹ * y a * w t) := by group
    _ = _ := by
      rw [he]
      simp only [neg_mul]

-- Lemma 39(d), calculated in the literal root words over any field.
private lemma torus_mul_of_add_eq_one (s t : Fˣ) (hst : (s : F) + (t : F) = 1) :
    h s * h t = h (s * t) := by
  have hi : -(((s * t)⁻¹ : Fˣ) : F) + ((s⁻¹ : Fˣ) : F) * ((t⁻¹ : Fˣ) : F) ^ 2 =
      ((t⁻¹ : Fˣ) : F) ^ 2 := by
    simp only [_root_.mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
    linear_combination -hst
  have hj : -(((s * t)⁻¹ : Fˣ) : F) + ((t⁻¹ : Fˣ) : F) = -((s⁻¹ : Fˣ) : F) := by
    simp only [_root_.mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
    linear_combination hst
  have hk : ((t⁻¹ : Fˣ) : F) + -((s : F) * ((t⁻¹ : Fˣ) : F)) = 1 := by
    simp only [Units.val_inv_eq_inv_val]
    field_simp
    linear_combination -hst
  have he : w (s * t) * w (-t) = h s := by
    calc
      w (s * t) * w (-t) = x s * (x (-(s : F)) * w (s * t)) * w (-t) := by
        rw [← mul_assoc, generator_relations.add, add_neg_cancel, generator_relations.zero, one_mul]
      _ = x s * (w (s * t) * y (((s⁻¹ : Fˣ) : F) * ((t⁻¹ : Fˣ) : F) ^ 2)) * w (-t) := by
        rw [root_mul_weyl]
        congr 3
        simp only [_root_.mul_inv_rev, Units.val_mul, Units.val_inv_eq_inv_val]
        field_simp
      _ = x s * y (-(((s * t)⁻¹ : Fˣ) : F)) * x (s * t : Fˣ) * y (((t⁻¹ : Fˣ) : F) ^ 2) * w (-t) := by
        rw [weyl_alternate i j hij (s * t)]
        simp only [← mul_assoc]
        rw [mul_assoc (x _ * y _ * x _) (y _) (y _), generator_relations.add, hi]
      _ = x s * y (-(((s * t)⁻¹ : Fˣ) : F)) * w (-t) * y (-((s : F) * ((t⁻¹ : Fˣ) : F))) * x (-1) := by
        rw [mul_assoc _ (y _) (w _), opposite_mul_weyl]
        rw [← mul_assoc _ (w _) (x _), mul_assoc _ (x _) (w _), root_mul_weyl]
        simp only [Units.val_neg, Units.val_mul, Units.val_inv_eq_inv_val, inv_neg]
        have h1 : - -(t : F) * ((t : F)⁻¹ ^ 2) * -(t : F) = -1 := by field_simp
        have h2 : - -((t : F)⁻¹) * ((s : F) * (t : F)) * -((t : F)⁻¹) =
            -((s : F) * (t : F)⁻¹) := by field_simp
        simp only [h1, h2, mul_assoc]
      _ = x s * y (-((s⁻¹ : Fˣ) : F)) * x (-(t : F)) * y 1 * x (-1) := by
        rw [weyl_alternate i j hij (-t)]
        simp only [Units.val_inv_eq_inv_val, Units.val_neg, inv_neg, neg_neg]
        simp only [Units.val_inv_eq_inv_val] at hj hk
        simp only [← mul_assoc]
        rw [mul_assoc (x _) (y _) (y _), generator_relations.add, hj]
        rw [mul_assoc (x _ * y _ * x _) (y _) (y _), generator_relations.add, hk]
      _ = h s := by
        have ht : -(t : F) = (s : F) + -1 := by linear_combination -hst
        rw [ht, ← generator_relations.add]
        simp [torus, torusWord, weylWord, mul_assoc]
  have he' : h (s * t) * (h t)⁻¹ = h s := by
    simp only [torus, torusWord, _root_.mul_inv_rev, mul_assoc, mul_inv_cancel_left]
    rw [weylWord_inv generator_relations]
    exact he
  exact (mul_inv_eq_iff_eq_mul.mp he').symm

private lemma torus_mul_square_right_iff [Finite F] (s t u : Fˣ) :
    (h s * h (t * u ^ 2) = h (s * (t * u ^ 2))) ↔ (h s * h t = h (s * t)) := by
  rw [← mul_assoc s t (u ^ 2), ← torus_mul_square i j hij (s * t) u,
    ← torus_mul_square i j hij t u, ← mul_assoc, mul_right_cancel_iff]

private lemma torus_mul_square_left_iff [Finite F] (s t u : Fˣ) :
    (h (s * u ^ 2) * h t = h ((s * u ^ 2) * t)) ↔ (h s * h t = h (s * t)) := by
  rw [(torus_commute i j hij (s * u ^ 2) t).eq, mul_comm (s * u ^ 2) t,
    torus_mul_square_right_iff, (torus_commute i j hij t s).eq, mul_comm t s]

/-- The finite-field relation (C) follows from the existing Steinberg relations,
including in characteristics two and three and without any cardinal lower bound. -/
theorem torusMultiplicative [Finite F] : TorusMultiplicative F := by
  intro i j hij s t
  by_cases ht : IsSquare t
  · obtain ⟨u, hu⟩ := ht.exists_sq
    rw [hu]
    exact torus_mul_square i j hij s u
  by_cases hs : IsSquare s
  · obtain ⟨u, hu⟩ := hs.exists_sq
    rw [hu, (torus_commute i j hij (u ^ 2) t).eq, mul_comm (u ^ 2) t]
    exact torus_mul_square i j hij t u
  have ht' : ¬IsSquare (t : F) := mt (FiniteTorus.unit_isSquare_iff t).mpr ht
  have hs' : ¬IsSquare (s : F) := mt (FiniteTorus.unit_isSquare_iff s).mpr hs
  have hchar : ringChar F ≠ 2 := fun hc => ht' (FiniteField.isSquare_of_char_two hc _)
  obtain ⟨a, b, ha, hb, hab⟩ := FiniteTorus.exists_nonsquares_add_one hchar
  have ha0 : a ≠ 0 := fun he => ha (he.symm ▸ IsSquare.zero)
  have hb0 : b ≠ 0 := fun he => hb (he.symm ▸ IsSquare.zero)
  let a' := Units.mk0 a ha0
  let b' := Units.mk0 b hb0
  have hsa : IsSquare (s / a') := (FiniteTorus.unit_isSquare_iff _).mpr
    (by simpa [a'] using FiniteTorus.square_of_nonsquare_ratio hs' ha)
  have htb : IsSquare (t / b') := (FiniteTorus.unit_isSquare_iff _).mpr
    (by simpa [b'] using FiniteTorus.square_of_nonsquare_ratio ht' hb)
  obtain ⟨u, hu⟩ := hsa.exists_sq
  obtain ⟨v, hv⟩ := htb.exists_sq
  have he : s = a' * u ^ 2 := by rw [← hu]; simp
  have hf : t = b' * v ^ 2 := by rw [← hv]; simp
  rw [he, hf]
  apply (torus_mul_square_left_iff i j hij a' (b' * v ^ 2) u).mpr
  apply (torus_mul_square_right_iff i j hij a' b' v).mpr
  exact torus_mul_of_add_eq_one i j hij a' b' hab

end Matrix.PSL3.UniversalProjection.Faithfulness
