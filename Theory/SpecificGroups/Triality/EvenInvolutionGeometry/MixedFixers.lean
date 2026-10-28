module
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.Coefficients
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.OddExponent
public import Theory.SpecificGroups.Triality.ConcreteBruhat.CartanNormalizer
public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers.HighestRoot
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.NormalForm.UnipotentCocycle.Descent

/-!
# Mixed inner–coefficient fixers of binary triality's positive subgroup

Suppose an inner automorphism times a coefficient automorphism fixes the actual
positive subgroup U pointwise. Coefficient automorphisms preserve U, so the
inner conjugator normalizes U and hence lies in the proved Borel. Write it as
u*t using the genuine unipotent-times-torus factorization.

The positive subgroup centralizes the highest-root curve, while the torus
scales its parameter. The faithful map from the elementary central quotient
into the split Geck matrices therefore gives c * e(z) = z on the actual
q-Frobenius fixed field. Evaluation at one gives c = 1. Thus e is an
automorphism over that fixed field, and its cube is one because the extension
has degree three. In the quotient by inner automorphisms, the original actor
then has both odd order and two-power order, so it is trivial.

This proves the requested even-exponent innerness branch, and in fact works
at every positive exponent, including n = 1, without simplicity or perfectness
assumptions. The caller supplies the actual inner–coefficient expression;
transport to arbitrary Sylow subgroups belongs to the source assembly.
The highest-root scalar calculation extends the involution argument in
`StandardTwoRank/FourSemilinear/HighestRoot.lean` to two-power actors.

Sources: Aschbacher–Smith 16.1.6, printed p.1172 (`refs/quasithin.pdf`),
and the root/Borel and coefficient conventions of GLS3 §§2.3–2.5
(`refs/KGroup/GLS3/chapter2.tex`).
-/

public section
noncomputable section
namespace Triality.Standard.EvenInvolutionGeometry
open OuterOdd Parabolics ConcreteBruhat ConcreteBruhat.FixedDescent PositiveCoordinates
open RadicalCoordinates.Centers EvenField.NormalForm.UnipotentCocycle
namespace MixedFixers

private theorem coefficient_unipotent (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) :
    (unipotent P).map (coefficientAction P e).toMonoidHom = unipotent P := by
  have preserves (f : CoefficientAut P) {x : Carrier P} (hx : x ∈ unipotent P) :
      coefficientAction P f x ∈ unipotent P := by
    apply (mem_descend_iff P hp (positiveSubgroup P) _).mpr
    rw [carrierToSplit_coefficient]
    exact (coefficientSplit_positiveSubgroup P f).le
      ⟨_, (mem_descend_iff P hp (positiveSubgroup P) x).mp hx, rfl⟩
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact preserves e hx
  · intro x hx
    refine ⟨coefficientAction P e⁻¹ x, preserves e⁻¹ hx, ?_⟩
    change (coefficientAction P e * coefficientAction P e⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl

/-- The mixed fixation hypothesis places the inner conjugator in the actual Borel. -/
theorem conjugator_mem_borel (P : Parameters) (hp : P.prime = 2)
    (g : Carrier P) (e : CoefficientAut P)
    (hfix : ∀ x ∈ unipotent P, (MulAut.conj g * coefficientAction P e) x = x) :
    g ∈ borel P := by
  have hU : (unipotent P).map (MulAut.conj g * coefficientAction P e).toMonoidHom =
      unipotent P := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change (MulAut.conj g * coefficientAction P e) x ∈ unipotent P
      rw [hfix x hx]
      exact hx
    · intro x hx
      exact ⟨x, hx, hfix x hx⟩
  rw [← normalizer_unipotent_eq_borel P hp]
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  calc
    (unipotent P).map (MulAut.conj g).toMonoidHom =
        ((unipotent P).map (coefficientAction P e).toMonoidHom).map
          (MulAut.conj g).toMonoidHom := by rw [coefficient_unipotent P hp]
    _ = (unipotent P).map (MulAut.conj g * coefficientAction P e).toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    _ = unipotent P := hU

private theorem split_torus_scales_highest (P : Parameters) (hp : P.prime = 2)
    {t : SplitGroup P} (ht : t ∈ splitTorus P) :
    ∃ c : ExtensionField P, c ≠ 0 ∧ ∀ x,
      t * curve P 11 x * t⁻¹ = curve P 11 (c * x) := by
  induction ht using Subgroup.closure_induction with
  | mem t ht =>
    obtain ⟨i, s, rfl⟩ := ht
    exact ⟨_, zpow_ne_zero _ s.ne_zero, fun x => torusWord_curve_conjugate P hp i s 11 x⟩
  | one => exact ⟨1, one_ne_zero, by simp⟩
  | mul t u _ _ ht hu =>
    obtain ⟨c, hc, ht⟩ := ht
    obtain ⟨d, hd, hu⟩ := hu
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    intro x
    calc
      (t * u) * curve P 11 x * (t * u)⁻¹ = t * (u * curve P 11 x * u⁻¹) * t⁻¹ := by group
      _ = curve P 11 ((c * d) * x) := by rw [hu, ht, mul_assoc]
  | inv t _ ht =>
    obtain ⟨c, hc, ht⟩ := ht
    refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
    intro x
    have h := ht (c⁻¹ * x)
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul] at h
    rw [← h]
    group

/-- The highest-root curve detects the coefficient action on the actual base subfield. -/
theorem coefficient_fixes_base (P : Parameters) (hp : P.prime = 2)
    (g : Carrier P) (e : CoefficientAut P)
    (hfix : ∀ x ∈ unipotent P, (MulAut.conj g * coefficientAction P e) x = x) :
    ∀ z : fixedField P, e z.val = z.val := by
  have hg := conjugator_mem_borel P hp g e hfix
  obtain ⟨u, hu, t, ht, rfl⟩ := (borel_eq_mul P hp).le hg
  obtain ⟨c, _, hc⟩ := split_torus_scales_highest P hp
    ((mem_descend_iff P hp (splitTorus P) t).mp ht)
  have hscalar (z : fixedField P) : c * e z.val = z.val := by
    have hz := hfix (highestHom P hp (Multiplicative.ofAdd z))
      (highestRoot_le_unipotent P hp ((highestHom_range P hp).le
        ⟨Multiplicative.ofAdd z, rfl⟩))
    have hh := congrArg (carrierToSplit P hp) hz
    change carrierToSplit P hp ((u * t) * coefficientAction P e
      (toCarrier P (elementaryHighestHom P hp (Multiplicative.ofAdd z))) * (u * t)⁻¹) = _ at hh
    simp only [highestHom, MonoidHom.comp_apply, map_mul, map_inv, carrierToSplit_coefficient P hp,
      carrierToSplit_toCarrier P hp, elementaryHighestHom_val P hp, coefficientSplit_curve P e] at hh
    have hu' := (mem_descend_iff P hp (positiveSubgroup P) u).mp hu
    have hcomm := (Subgroup.mem_centralizer_iff.mp
      (positiveSubgroup_le_centralizer_highestCurve P (c * e z.val) hu'))
      _ (Set.mem_singleton _)
    have hre : (carrierToSplit P hp u * carrierToSplit P hp t) * curve P 11 (e z.val) *
        (carrierToSplit P hp u * carrierToSplit P hp t)⁻¹ = curve P 11 (c * e z.val) := by
      calc
        _ = carrierToSplit P hp u * (carrierToSplit P hp t * curve P 11 (e z.val) *
          (carrierToSplit P hp t)⁻¹) * (carrierToSplit P hp u)⁻¹ := by group
        _ = _ := by rw [hc, ← hcomm]; group
    apply highestCurve_injective P
    exact hre.symm.trans hh
  have hc1 : c = 1 := by simpa using hscalar 1
  intro z
  simpa only [hc1, one_mul] using hscalar z

/-- Mixed pointwise fixation leaves at most the odd cubic coefficient contribution. -/
theorem coefficient_cube_eq_one (P : Parameters) (hp : P.prime = 2)
    (g : Carrier P) (e : CoefficientAut P)
    (hfix : ∀ x ∈ unipotent P, (MulAut.conj g * coefficientAction P e) x = x) :
    e ^ 3 = 1 := by
  have hdegree : Module.finrank (fixedField P) (ExtensionField P) = 3 := by
    have hc := Module.natCard_eq_pow_finrank (K := fixedField P) (V := ExtensionField P)
    rw [card_extensionField, card_fixedField] at hc
    exact (Nat.pow_right_injective (by have := P.q_ge_two; omega)) hc.symm
  let f : ExtensionField P ≃ₐ[fixedField P] ExtensionField P :=
    AlgEquiv.ofRingEquiv (f := e) (coefficient_fixes_base P hp g e hfix)
  have hc : Nat.card (ExtensionField P ≃ₐ[fixedField P] ExtensionField P) = 3 := by
    rw [IsGalois.card_aut_eq_finrank, hdegree]
  have hf : f ^ 3 = 1 := by simpa only [hc] using (pow_card_eq_one' (x := f))
  exact congrArg AlgEquiv.toRingEquiv hf

end MixedFixers

/-- Every two-power actor with the supplied mixed expression fixing U pointwise is inner. -/
theorem inner_of_fixes_unipotent (n : ℕ) (hn : 0 < n)
    (a : MulAut (BinaryCarrier n hn)) {k : ℕ} (ha : a ^ (2 ^ k) = 1)
    (hform : ∃ g : BinaryCarrier n hn,
      ∃ e : CoefficientAut (binaryParameters n hn),
        a = MulAut.conj g * coefficientAction (binaryParameters n hn) e)
    (hfix : ∀ x ∈ unipotent (binaryParameters n hn), a x = x) :
    ∃ x : BinaryCarrier n hn, a = MulAut.conj x := by
  let P := binaryParameters n hn
  let I := (MulAut.conj : BinaryCarrier n hn →* MulAut (BinaryCarrier n hn)).range
  let q := QuotientGroup.mk' I
  obtain ⟨g, e, hform⟩ := hform
  have he : e ^ 3 = 1 := MixedFixers.coefficient_cube_eq_one P rfl g e
    (fun x hx => (congrArg (fun b : MulAut (BinaryCarrier n hn) => b x) hform).symm.trans
      (hfix x hx))
  have hq : q a = q (coefficientAction P e) := by
    rw [hform, map_mul, show q (MulAut.conj g) = 1 from
      (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩, one_mul]
  have hoddpow : (q a) ^ 3 = 1 := by
    rw [hq, ← map_pow, ← map_pow, he, map_one, map_one]
  have htwopow : (q a) ^ (2 ^ k) = 1 := by rw [← map_pow, ha, map_one]
  have horder : orderOf (q a) = 1 :=
    Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 3 2).pow_right k)
      (orderOf_dvd_of_pow_eq_one hoddpow) (orderOf_dvd_of_pow_eq_one htwopow)
  obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff a).mp (orderOf_eq_one_iff.mp horder)
  exact ⟨x, hx.symm⟩

/-- The even-exponent mixed Sylow-fixer case of source 16.1.6. -/
theorem inner_of_even_exponent (n : ℕ) (hn : 0 < n) (_heven : Even n)
    (a : MulAut (BinaryCarrier n hn)) {k : ℕ} (ha : a ^ (2 ^ k) = 1)
    (hform : ∃ g : BinaryCarrier n hn,
      ∃ e : CoefficientAut (binaryParameters n hn),
        a = MulAut.conj g * coefficientAction (binaryParameters n hn) e)
    (hfix : ∀ x ∈ unipotent (binaryParameters n hn), a x = x) :
    ∃ x : BinaryCarrier n hn, a = MulAut.conj x :=
  inner_of_fixes_unipotent n hn a ha hform hfix

end Triality.Standard.EvenInvolutionGeometry
