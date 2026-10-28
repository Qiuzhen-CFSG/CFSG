module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.CommutatorCheck.Comparison
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.CommutatorCheck.Check

/-!
# Soundness of the J₂ commutator certificate

The packed actions are the actual published carrier words by `Comparison`.
Group identities force the short point tests to pass. The full fourth-power
point test then proves equality of permutations, and injectivity of the
carrier inclusion gives the required group identity. The replacement of the
inverse by the square uses precisely the input cube identity. The general
action lemmas keep the kernel from unfolding the large concrete word tables
while checking this algebraic argument.
-/

public section
set_option Elab.async false
namespace Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion.CommutatorCheck

theorem pairValue_eq (i : Fin 1920) (j : Fin 315) (p : Fin 100) :
    pairValue i j p = inclusion (pairRepresentative i j) p := by
  rw [pairValue, centralValue_eq, repValue_eq, pairRepresentative, map_mul]
  rfl

theorem involutionValue_eq (p : Fin 100) : involutionValue p = inclusion t p := by
  rw [involutionValue, value_zero, inclusion_t]

theorem iterate_eq (f : Fin 100 → Fin 100) (g : Carrier)
    (hf : ∀ p, f p = inclusion g p) (n : Nat) (p : Fin 100) :
    f^[n] p = inclusion (g ^ n) p := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih, hf, pow_succ, map_mul]
    rfl

private theorem shortTest_of_actions (f : Fin 100 → Fin 100) (u v : Carrier)
    (hf : ∀ p, f p = inclusion v p)
    (hu : ∀ p, involutionValue p = inclusion u p)
    (h3 : v ^ 3 = 1) (h7 : (u * v) ^ 7 = 1) : shortTest f = true := by
  apply (checkFin_iff _).mpr
  intro p
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [iterate_eq _ _ hf, h3, map_one]
    rfl
  · apply decide_eq_true
    have hm (q : Fin 100) : involutionValue (f q) = inclusion (u * v) q := by
      simp only [hu, hf, map_mul, Equiv.Perm.mul_apply]
    rw [iterate_eq _ _ hm, h7, map_one]
    rfl

theorem shortTest_of (i : Fin 1920) (j : Fin 315)
    (h3 : pairRepresentative i j ^ 3 = 1)
    (h7 : (t * pairRepresentative i j) ^ 7 = 1) :
    shortTest (pairValue i j) = true :=
  shortTest_of_actions (pairValue i j) t (pairRepresentative i j)
    (pairValue_eq i j) involutionValue_eq h3 h7

private theorem fourthTest_sound (f : Fin 100 → Fin 100) (u v : Carrier)
    (hf : ∀ p, f p = inclusion v p)
    (hu : ∀ p, involutionValue p = inclusion u p)
    (h3 : v ^ 3 = 1) (h4 : fourthTest f = true) :
    (u * v * u * v⁻¹) ^ 4 = 1 := by
  have hinv : v⁻¹ = v * v := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using h3
  have hm (q : Fin 100) :
      involutionValue (f (involutionValue (f (f q)))) =
        inclusion (u * v * u * v⁻¹) q := by
    simp only [hu, hf, hinv, map_mul, Equiv.Perm.mul_apply]
  apply inclusion_injective
  apply Equiv.ext
  intro p
  have hp := of_decide_eq_true ((checkFin_iff _).mp h4 p)
  rw [iterate_eq _ _ hm] at hp
  simpa only [map_pow, map_one, Equiv.Perm.one_apply] using hp

theorem checkPair_sound (i : Fin 1920) (j : Fin 315) (hc : checkPair i j = true)
    (h3 : pairRepresentative i j ^ 3 = 1)
    (h7 : (t * pairRepresentative i j) ^ 7 = 1) :
    (t * pairRepresentative i j * t * (pairRepresentative i j)⁻¹) ^ 4 = 1 := by
  have hs := shortTest_of i j h3 h7
  have h4 : fourthTest (pairValue i j) = true := by
    simpa only [checkPair, hs, Bool.not_true, Bool.false_or] using hc
  exact fourthTest_sound (pairValue i j) t (pairRepresentative i j)
    (pairValue_eq i j) involutionValue_eq h3 h4

theorem checkRows_sound (lo count : Nat) (h : checkRows lo count = true)
    (i : Fin 1920) (j : Fin 315) (hlo : lo ≤ i.val) (hhi : i.val < lo + count) :
    checkPair i j = true :=
  (checkFin_iff _).mp (checkRange_sound rowCheck lo count h i hlo hhi) j

end Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion.CommutatorCheck
