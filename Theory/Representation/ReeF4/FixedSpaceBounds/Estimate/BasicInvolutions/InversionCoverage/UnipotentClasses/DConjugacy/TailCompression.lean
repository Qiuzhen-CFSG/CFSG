module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.Reduction
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.Middle
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.Weyl
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.TailCompression.First
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy.TailCompression.SuzukiWeyl

/-!
# Compressing the elementary Ree involution tail

Every literal tail x₆(a)x₄(b)y₅(c)y₇(d)y₃(e) has a conjugate supported on
x₄, y₅ and y₃. No nonidentity or square premise is required.

For d ≠ 0, first-curve conjugation kills a, and two further first-curve
conjugations kill b. The resulting central pair is moved to the desired
subspace by solving t²θ(t) = e/d and applying the fixed Suzuki Weyl word.
The identity θ²(t) = t² makes tθ(t) injective and hence surjective; composing
with θ proves that the power equation always has a solution. The d = 0
cases either already transport by Weyl or acquire a nonzero fourth
coordinate after one first-curve conjugation and Weyl transport.

`root_classes_tail` applies the existing middle-tail conjugators to the
result. This discharges the tail-compression premise in the separate D
involution assembly; transport from D to D₂ remains that assembly's task.

Source: GLS3 Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`;
GLS3 Lemma 3.3.9 supplies the tail convention. The conjugacy calculation
feeds Guralnick–Malle, Classification of 2F-modules II, Lemma 8.8, p.57.
-/

@[expose] public section
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy
open NormalizedRootCentralizers.CenterExponent
open ElementaryTwoBound ElementaryTwoBound.RootCalculations EvenInvolutionGeometry
open Parabolics.Binary.FixedGeometry
namespace TailCompression

private theorem norm_surjective (m : ℕ) :
    Function.Surjective (fun t : CoefficientField m => t * titsEnd m t) := by
  apply Finite.surjective_of_injective
  intro a b hab
  change a * titsEnd m a = b * titsEnd m b at hab
  have hn (x : CoefficientField m) :
      titsEnd m (x * titsEnd m x) = x * (x * titsEnd m x) := by
    rw [map_mul, titsEnd_twice]
    ring
  by_cases ha : a = 0
  · subst a
    have hb : b = 0 := (mul_eq_zero.mp (show b * titsEnd m b = 0 by
      simpa only [zero_mul] using hab.symm)).elim id
      (fun h => (titsEnd m).injective (by simpa using h))
    exact hb.symm
  · apply mul_right_cancel₀ (mul_ne_zero ha ((map_ne_zero (titsEnd m)).mpr ha))
    calc
      a * (a * titsEnd m a) = titsEnd m (a * titsEnd m a) := (hn a).symm
      _ = titsEnd m (b * titsEnd m b) := congrArg (titsEnd m) hab
      _ = b * (a * titsEnd m a) := by rw [hn, hab]

private theorem twisted_norm_surjective (m : ℕ) :
    Function.Surjective (fun t : CoefficientField m => t ^ 2 * titsEnd m t) := by
  intro k
  obtain ⟨s, hs⟩ := (titsAutomorphism m).surjective k
  obtain ⟨t, ht⟩ := norm_surjective m s
  refine ⟨t, ?_⟩
  have he : titsEnd m s = k := hs
  rw [← ht, map_mul, titsEnd_twice] at he
  rwa [mul_comm] at he

-- Assemble the two concrete identities proved in the dedicated leaves.
variable (m : ℕ)
variable (first : ∀ t a b c d e : CoefficientField m,
    IsConj (tailElement m ![a,b,c,d,e])
      (tailElement m ![a+t*d, b+(a+t*d)*titsEnd m t,
        c+t*titsEnd m a, d, e+t*b+t^2*titsEnd m t*d]))
variable (weyl : ∀ a b c d e : CoefficientField m,
    IsConj (tailElement m ![a,b,c,d,e]) (tailElement m ![b,a,c,e,d]))

include first in
private theorem central_conj (s a b c d e : CoefficientField m) :
    IsConj (tailElement m ![a,b,c,d,e])
      (tailElement m ![a,b+s*d,c+s*titsEnd m d,d,e+s*a+titsEnd m s*d]) := by
  obtain ⟨t, rfl⟩ := norm_surjective m s
  have h := (first t a b c d e).trans
    (first t (a+t*d) (b+(a+t*d)*titsEnd m t) (c+t*titsEnd m a)
      d (e+t*b+t^2*titsEnd m t*d))
  have hthree : (3 : CoefficientField m) = 1 := by
    linear_combination (CharTwo.two_eq_zero (R := CoefficientField m))
  convert h using 1
  congr 1
  ext i
  fin_cases i <;> dsimp <;> (try simp only [map_add, map_mul, titsEnd_twice]) <;>
    ring_nf <;> simp only [CharTwo.two_eq_zero, hthree, mul_zero, mul_one, add_zero]

include first weyl in
private theorem nonzero_fourth (a b c d e : CoefficientField m) (hd : d ≠ 0) :
    ∃ b' c' e', IsConj (tailElement m ![a,b,c,d,e])
      (tailElement m ![0,b',c',0,e']) := by
  have ha : a + (a / d) * d = 0 := by
    rw [div_mul_cancel₀ _ hd, CharTwo.add_self_eq_zero]
  have h1 := first (a / d) a b c d e
  simp only [ha, zero_mul, add_zero] at h1
  let c₁ := c + (a / d) * titsEnd m a
  let e₁ := e + (a / d) * b + (a / d)^2 * titsEnd m (a / d) * d
  have hb : b + (b / d) * d = 0 := by
    rw [div_mul_cancel₀ _ hd, CharTwo.add_self_eq_zero]
  have h2 := central_conj m first (b / d) 0 b c₁ d e₁
  simp only [hb, mul_zero, add_zero] at h2
  let c₂ := c₁ + (b / d) * titsEnd m d
  let e₂ := e₁ + titsEnd m (b / d) * d
  obtain ⟨t, ht⟩ := twisted_norm_surjective m (e₂ / d)
  change t ^ 2 * titsEnd m t = e₂ / d at ht
  have he : e₂ + t^2*titsEnd m t*d = 0 := by
    rw [ht, div_mul_cancel₀ _ hd, CharTwo.add_self_eq_zero]
  have h3 := first t 0 0 c₂ d e₂
  simp only [zero_add, map_zero, mul_zero, add_zero, he] at h3
  have h4 := central_conj m first (t * titsEnd m t) (t*d)
    (t*d*titsEnd m t) c₂ d 0
  have hb' : t*d*titsEnd m t + t*titsEnd m t*d = 0 := by
    have hh : t*d*titsEnd m t = t*titsEnd m t*d := by ring
    rw [hh, CharTwo.add_self_eq_zero]
  have he' : 0 + t*titsEnd m t*(t*d) + titsEnd m (t*titsEnd m t)*d = 0 := by
    rw [map_mul, titsEnd_twice]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero]
  rw [hb', he'] at h4
  refine ⟨t*d, c₂ + (t*titsEnd m t)*titsEnd m d, d, ?_⟩
  exact (((h1.trans h2).trans h3).trans h4).trans (weyl _ _ _ _ _)

include first weyl in
/-- Algebraic compression from the two literal transport identities. -/
private theorem compress_of_identities : CompressTail m := by
  intro v
  have hv : v = ![v 0,v 1,v 2,v 3,v 4] := by ext i; fin_cases i <;> rfl
  rw [hv]
  suffices ∃ b c e, IsConj (tailElement m ![v 0,v 1,v 2,v 3,v 4])
      (tailElement m ![0,b,c,0,e]) by
    obtain ⟨b,c,e,h⟩ := this
    obtain ⟨g,hg⟩ := isConj_iff.mp h
    exact ⟨g,b,c,e,hg⟩
  by_cases hd : v 3 = 0
  · by_cases he : v 4 = 0
    · by_cases hb : v 1 = 0
      · refine ⟨v 0,v 2,0, ?_⟩
        simpa only [hd,he,hb] using weyl (v 0) 0 (v 2) 0 0
      · have h1 := first 1 (v 0) (v 1) (v 2) 0 0
        simp only [one_mul, mul_zero, add_zero, zero_add] at h1
        have h2 := weyl (v 0) (v 1 + v 0 * titsEnd m 1)
          (v 2 + titsEnd m (v 0)) 0 (v 1)
        obtain ⟨b,c,e,h⟩ := nonzero_fourth m first weyl
          (v 1 + v 0 * titsEnd m 1) (v 0) (v 2 + titsEnd m (v 0)) (v 1) 0 hb
        refine ⟨b,c,e, ?_⟩
        simpa only [hd,he] using (h1.trans h2).trans h
    · obtain ⟨b,c,e,h⟩ := nonzero_fourth m first weyl (v 1) (v 0) (v 2) (v 4) 0 he
      refine ⟨b,c,e, ?_⟩
      simpa only [hd] using (weyl (v 0) (v 1) (v 2) 0 (v 4)).trans h
  · exact nonzero_fourth m first weyl (v 0) (v 1) (v 2) (v 3) (v 4) hd
end TailCompression

/-- Every elementary tail has a conjugate supported on x₄, y₅ and y₃.
The witnesses are words in the first root curve and the fixed Suzuki Weyl lift. -/
theorem compressTail (m : ℕ) (_hm : 1 ≤ m) : CompressTail m := by
  apply TailCompression.compress_of_identities m
  · intro t a b c d e
    apply isConj_iff.mpr
    exact ⟨(mainElement m 0 t)⁻¹, by
      simpa only [MulAut.conj_apply, inv_inv] using
        TailCompression.first_conj_tail m t a b c d e⟩
  · intro a b c d e
    exact isConj_iff.mpr ⟨weylLift m .suzuki,
      TailCompression.suzukiWeyl_tail m a b c d e⟩

/-- Apply compression to the literal tail in the involution branch: the
previously constructed middle conjugators now classify every nonidentity tail. -/
theorem root_classes_tail (m : ℕ) (hm : 1 ≤ m)
    (v : Fin 5 → CoefficientField m) (hne : tailElement m v ≠ 1) :
    IsLongRootInvolution (tailElement m v) ∨ IsShortRootInvolution (tailElement m v) := by
  obtain ⟨g,b,c,e,hg⟩ := compressTail m hm v
  have hc : IsConj (tailElement m v) (tailElement m ![0,b,c,0,e]) :=
    isConj_iff.mpr ⟨g,hg⟩
  have hne' : tailElement m ![0,b,c,0,e] ≠ 1 := by
    intro he
    exact hne ((MulAut.conj g).injective (hg.trans (he.trans (map_one _).symm)))
  rcases root_classes_middle m b c e hne' with ⟨a,ha,h⟩ | ⟨a,ha,h⟩
  · exact Or.inl ⟨a,ha,h.trans hc.symm⟩
  · exact Or.inr ⟨a,ha,h.trans hc.symm⟩

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage.UnipotentClasses.DConjugacy
