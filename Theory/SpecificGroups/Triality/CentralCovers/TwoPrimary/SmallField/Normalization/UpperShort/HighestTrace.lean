module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.UpperShort.Transport
public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.TorusMotion.Weights
public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.CentralHigherGeneration.Exchange

/-!
# The highest short-root trace formula in central covers of ³D₄(2)

For additive root sections satisfying the ten commuting pairs, let C(s,t)
be the commutator of short roots 1 and 2. The arms coordinate law gives its
projection, and exact commutation with the highest section makes C additive.
The arms torus has weights a² and a⁻¹. Its lifts centralize C: the projected
highest root is also a commutator of the first two long roots, both fixed by
the torus. Independence of commutators from central changes of lifts then
gives C(s,t) = Q(s F(t)), where Q(x) = C(x,1).

Conjugate two commuting values of short root 1 by short root 0 at one.
The actual first-short-pair exchange and the commuting pairs imply
C(1,F(t)+t) = 1. Thus Q(F(t)) = Q(t), so Q factors through the cubic trace.
The binary section of Q(1) is precisely the ORIGINAL chosen highest section.
No comparison with the lifted long-pair commutator is assumed or proved here.

The argument works in every central extension with the specified commuting
pairs; the final theorem applies it to the canonical universal projection.
Sources: GLS3 §2.4.5(b)(2),(4) and §6.1
(`refs/KGroup/GLS3/chapter2.tex`, `chapter6.tex`); Aschbacher–Smith I.1.3
(`refs/quasithin.pdf`, printed p.407 / PDF p.418).
-/

public section

open Triality.Standard Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat
open Triality.Standard.PositiveCoordinates
open Triality.Standard.RadicalCoordinates Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.RadicalCoordinates.LeviCommutators
open scoped commutatorElement
namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField.UpperShort
noncomputable section
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "hP" => binaryParameters_prime 1 Nat.zero_lt_one
local notation "G" => BinaryCarrier 1 Nat.zero_lt_one
local notation "F" => ExtensionField P

private def armsValue (v : ArmsParameters P) : G := (armsEquiv P hP v).val

private theorem armsValue_factorization (v : ArmsParameters P) :
    armsValue v = long P hP 0 (v.2 0) * short P hP 1 (v.1 0) *
      short P hP 2 (v.1 1) * long P hP 1 (v.2 1) * long P hP 2 (v.2 2) := by
  have hv : armsValue v = toCarrier P (rootElement P hP .arms v) := rfl
  rw [hv, rootElement_factorization]
  simp [extendOrbit]

private theorem armsValue_commutator (v w : ArmsParameters P) :
    ⁅armsValue v, armsValue w⁆ = long P hP 2 (armsCommutator P v w) := by
  have h := congrArg (armsSubgroup P).subtype (armsEquiv_commutator P hP v w)
  change ⁅armsValue v, armsValue w⁆ = _ at h
  rw [h]
  change armsValue (centralParameters P _) = _
  rw [armsValue_factorization]
  simp [centralParameters]

private theorem base_short_pair (s t : F) :
    ⁅short P hP 1 s, short P hP 2 t⁆ =
      long P hP 2 (cubicTrace P (s * fieldFrobenius P t)) := by
  have h := armsValue_commutator (![s,0], 0) (![0,t], 0)
  simpa [armsValue_factorization, armsCommutator, armsCocycle, armsPairing,
    -fieldFrobenius_apply] using h

private theorem base_long_pair (s : fixedField P) :
    ⁅long P hP 0 s, long P hP 1 1⁆ = long P hP 2 s := by
  have h := armsValue_commutator (0, ![s,0,0]) (0, ![0,1,0])
  simpa [armsValue_factorization, armsCommutator, armsCocycle] using h

private theorem small_norm (a : Fˣ) : cubicNorm P a.val = 1 := by
  rcases fixedField_cases (cubicNorm P a.val) with h | h
  · have hv := congrArg Subtype.val h
    change a.val * fieldFrobenius P a.val * fieldFrobenius P (fieldFrobenius P a.val) = 0 at hv
    exact False.elim ((mul_ne_zero (mul_ne_zero a.ne_zero
      ((map_ne_zero (fieldFrobenius P)).mpr a.ne_zero))
      ((map_ne_zero (fieldFrobenius P)).mpr ((map_ne_zero (fieldFrobenius P)).mpr a.ne_zero))) hv)
  · exact h

private theorem small_weights (a : Fˣ) :
    a.val / (fieldFrobenius P a.val * fieldFrobenius P (fieldFrobenius P a.val)) = a.val ^ 2 ∧
    a.val * fieldFrobenius P a.val / fieldFrobenius P (fieldFrobenius P a.val) = a.val⁻¹ := by
  have hn := congrArg Subtype.val (small_norm a)
  change a.val * fieldFrobenius P a.val * fieldFrobenius P (fieldFrobenius P a.val) = 1 at hn
  have hF (x : F) : fieldFrobenius P x = x ^ 2 := rfl
  simp only [hF, ← pow_mul] at hn ⊢
  have ht := a.ne_zero
  constructor
  · field_simp
    linear_combination -hn
  · field_simp

private theorem torus_short_one (a : Fˣ) (s : F) :
    torusActor P hP .arms a * short P hP 1 s * (torusActor P hP .arms a)⁻¹ =
      short P hP 1 (a.val ^ 2 * s) := by
  simp only [torusActor, short, ← map_mul, ← map_inv]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul, map_inv, shortElementary_val]
  simpa only [(small_weights a).1] using torus_arms_short_one_conjugate P hP a s

private theorem torus_short_two (a : Fˣ) (s : F) :
    torusActor P hP .arms a * short P hP 2 s * (torusActor P hP .arms a)⁻¹ =
      short P hP 2 (a.val⁻¹ * s) := by
  simp only [torusActor, short, ← map_mul, ← map_inv]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul, map_inv, shortElementary_val]
  simpa only [(small_weights a).2] using torus_arms_short_two_conjugate P hP a s

private theorem torus_long (a : Fˣ) (i : Fin 3) (hi : i = 0 ∨ i = 1)
    (s : fixedField P) :
    Commute (torusActor P hP .arms a) (long P hP i s) := by
  apply mul_inv_eq_iff_eq_mul.mp
  simp only [torusActor, long, ← map_mul, ← map_inv]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul, map_inv, longElementary_val]
  rcases hi with rfl | rfl
  · simpa only [small_norm, inv_one, one_mul] using torus_arms_long_zero_conjugate P hP a s
  · simpa only [small_norm, one_mul] using torus_arms_long_one_conjugate P hP a s

variable {E : Type*} [Group E] {f : E →* G}

private theorem commute_commutator_of_images (hk : f.ker ≤ Subgroup.center E)
    (a b c : E) (ha : Commute (f c) (f a)) (hb : Commute (f c) (f b)) :
    Commute c ⁅a,b⁆ := by
  apply mul_inv_eq_iff_eq_mul.mp
  rw [conjugate_commutatorElement]
  apply CentralExtension.commutator_eq_of_image_eq f hk
  · simp only [map_mul, map_inv]
    rw [ha.eq, mul_inv_cancel_right]
  · simp only [map_mul, map_inv]
    rw [hb.eq, mul_inv_cancel_right]

private theorem short_long (L : RootSections 1 Nat.zero_lt_one f)
    (hc : CommutingPairs L) (i j : Fin 3) (hi : i ≠ 0) (s : F) (t : fixedField P) :
    Commute (L.shortRoot i (.ofAdd s)) (L.longRoot j (.ofAdd t)) := by
  fin_cases i
  · exact False.elim (hi rfl)
  all_goals fin_cases j
  all_goals
    first
    | simpa [RootSections.factor] using hc 2 1 (![0,s,0],0) (0,![t,0,0]) (by decide) (by simp [interactingPair])
    | simpa [RootSections.factor] using hc 2 4 (![0,s,0],0) (0,![0,t,0]) (by decide) (by simp [interactingPair])
    | simpa [RootSections.factor] using hc 2 5 (![0,s,0],0) (0,![0,0,t]) (by decide) (by simp [interactingPair])
    | simpa [RootSections.factor] using hc 3 1 (![0,0,s],0) (0,![t,0,0]) (by decide) (by simp [interactingPair])
    | simpa [RootSections.factor] using hc 3 4 (![0,0,s],0) (0,![0,t,0]) (by decide) (by simp [interactingPair])
    | simpa [RootSections.factor] using hc 3 5 (![0,0,s],0) (0,![0,0,t]) (by decide) (by simp [interactingPair])

private def pairing (L : RootSections 1 Nat.zero_lt_one f) (s t : F) : E :=
  ⁅L.shortRoot 1 (.ofAdd s), L.shortRoot 2 (.ofAdd t)⁆

private theorem pairing_project (L : RootSections 1 Nat.zero_lt_one f) (s t : F) :
    f (pairing L s t) = long P hP 2 (cubicTrace P (s * fieldFrobenius P t)) := by
  simp only [pairing, map_commutatorElement, L.project_short, base_short_pair]

private theorem short_pairing_commute (hk : f.ker ≤ Subgroup.center E)
    (L : RootSections 1 Nat.zero_lt_one f) (hc : CommutingPairs L)
    (i : Fin 3) (hi : i ≠ 0) (s t u : F) :
    Commute (L.shortRoot i (.ofAdd s)) (pairing L t u) := by
  apply commutatorElement_eq_one_iff_commute.mp
  rw [CentralExtension.commutator_eq_of_image_eq f hk rfl
    ((pairing_project L t u).trans (L.project_long 2 _).symm)]
  exact (short_long L hc i 2 hi s _).commutator_eq

private theorem pairing_add_left (hk : f.ker ≤ Subgroup.center E)
    (L : RootSections 1 Nat.zero_lt_one f) (hc : CommutingPairs L) (s t u : F) :
    pairing L (s+t) u = pairing L s u * pairing L t u := by
  simp only [pairing, ofAdd_add, map_mul, commutatorElement_mul_left_eq_conj_mul]
  change L.shortRoot 1 (.ofAdd s) * pairing L t u * (L.shortRoot 1 (.ofAdd s))⁻¹ *
    pairing L s u = _
  rw [(short_pairing_commute hk L hc 1 (by decide) s t u).eq, mul_inv_cancel_right]
  apply Commute.eq
  have h1 := short_pairing_commute hk L hc 1 (by decide) t s u
  have h2 := short_pairing_commute hk L hc 2 (by decide) u s u
  exact ((h1.mul_left h2).mul_left h1.inv_left).mul_left h2.inv_left


private theorem pairing_torus (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (L : RootSections 1 Nat.zero_lt_one f)
    (a : Fˣ) (s t : F) :
    pairing L (a.val ^ 2 * s) (a.val⁻¹ * t) = pairing L s t := by
  obtain ⟨z, hz⟩ := hf (torusActor P hP .arms a)
  let u := L.longRoot 0 (.ofAdd (cubicTrace P (s * fieldFrobenius P t)))
  let v := L.longRoot 1 (.ofAdd 1)
  have hu : Commute (f z) (f u) := by
    rw [hz, L.project_long]
    exact torus_long a 0 (Or.inl rfl) _
  have hv : Commute (f z) (f v) := by
    rw [hz, L.project_long]
    exact torus_long a 1 (Or.inr rfl) _
  have hproj : f (pairing L s t) = f ⁅u,v⁆ := by
    rw [pairing_project, map_commutatorElement, L.project_long, L.project_long, base_long_pair]
  have hfix : Commute z (pairing L s t) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [CentralExtension.commutator_eq_of_image_eq f hk rfl hproj]
    exact (commute_commutator_of_images hk u v z hu hv).commutator_eq
  calc
    pairing L (a.val ^ 2 * s) (a.val⁻¹ * t) = z * pairing L s t * z⁻¹ := by
      rw [pairing, pairing, conjugate_commutatorElement]
      apply CentralExtension.commutator_eq_of_image_eq f hk
      · simp only [map_mul, map_inv, L.project_short, hz, torus_short_one]
      · simp only [map_mul, map_inv, L.project_short, hz, torus_short_two]
    _ = pairing L s t := hfix.mul_inv_cancel

private theorem pairing_reduce (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (L : RootSections 1 Nat.zero_lt_one f) (s t : F) :
    pairing L s t = pairing L (s * fieldFrobenius P t) 1 := by
  by_cases ht : t = 0
  · subst t
    simp [pairing, -fieldFrobenius_apply]
  · have h := pairing_torus hf hk L (Units.mk0 t ht) s t
    have hF : fieldFrobenius P t = t ^ 2 := rfl
    simpa only [hF, Units.val_mk0, inv_mul_cancel₀ ht, mul_comm (t ^ 2) s] using h.symm

private theorem long_long (L : RootSections 1 Nat.zero_lt_one f)
    (hc : CommutingPairs L) (i j : Fin 3) (hi : i = 1 ∨ i = 2)
    (hj : j = 1 ∨ j = 2) (s t : fixedField P) :
    Commute (L.longRoot i (.ofAdd s)) (L.longRoot j (.ofAdd t)) := by
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (Commute.all _ _).map _
  · simpa [RootSections.factor] using hc 4 5 (0,![0,s,0]) (0,![0,0,t]) (by decide) (by simp [interactingPair])
  · simpa [RootSections.factor] using hc 5 4 (0,![0,0,s]) (0,![0,t,0]) (by decide) (by simp [interactingPair])
  · exact (Commute.all _ _).map _

private theorem strip_right {a b c : E} (h : Commute a (b*c)) (hc : Commute a c) :
    Commute a b := by
  have hh := h.mul_right hc.inv_right
  simpa only [mul_inv_cancel_right] using hh

private theorem strip_left {a b c : E} (h : Commute a (b*c)) (hb : Commute a b) :
    Commute a c := by
  have hh := hb.inv_right.mul_right h
  simpa only [inv_mul_cancel_left] using hh

private def exchangeCorrection (L : RootSections 1 Nat.zero_lt_one f) (t : F) : E :=
  L.shortRoot 2 (.ofAdd (higherCoefficient P 1 t)) *
    L.longRoot 1 (.ofAdd (cubicTrace P (fieldFrobenius P (fieldFrobenius P t)))) *
    L.longRoot 2 (.ofAdd (cubicTrace P
      (fieldFrobenius P t * fieldFrobenius P (fieldFrobenius P t))))

private theorem exchange_image (L : RootSections 1 Nat.zero_lt_one f) (t : F) :
    f ((L.shortRoot 0 (.ofAdd 1))⁻¹ * L.shortRoot 1 (.ofAdd t) * L.shortRoot 0 (.ofAdd 1)) =
      f (L.shortRoot 1 (.ofAdd t) * (exchangeCorrection L t)⁻¹) := by
  simp only [map_mul, map_inv, L.project_short]
  have h := short_zero_one_exchange P hP 1 t
  simp only [map_one, one_mul] at h
  have hk : f (exchangeCorrection L t) =
      short P hP 2 (higherCoefficient P 1 t) *
        long P hP 1 (cubicTrace P (fieldFrobenius P (fieldFrobenius P t))) *
        long P hP 2 (cubicTrace P
          (fieldFrobenius P t * fieldFrobenius P (fieldFrobenius P t))) := by
    simp only [exchangeCorrection, map_mul, L.project_short, L.project_long]
  rw [hk]
  calc
    _ = (short P hP 0 1)⁻¹ *
        (short P hP 1 t * short P hP 0 1 *
          short P hP 2 (higherCoefficient P 1 t) *
          long P hP 1 (cubicTrace P (fieldFrobenius P (fieldFrobenius P t))) *
          long P hP 2 (cubicTrace P
            (fieldFrobenius P t * fieldFrobenius P (fieldFrobenius P t)))) *
        (short P hP 2 (higherCoefficient P 1 t) *
          long P hP 1 (cubicTrace P (fieldFrobenius P (fieldFrobenius P t))) *
          long P hP 2 (cubicTrace P
            (fieldFrobenius P t * fieldFrobenius P (fieldFrobenius P t))))⁻¹ := by group
    _ = _ := by rw [← h]; group

private theorem pairing_vanish (hk : f.ker ≤ Subgroup.center E)
    (L : RootSections 1 Nat.zero_lt_one f) (hc : CommutingPairs L) (t : F) :
    pairing L 1 (fieldFrobenius P t + t) = 1 := by
  let z := L.shortRoot 0 (.ofAdd 1)
  let y := fun t : F => L.shortRoot 1 (.ofAdd t) * (exchangeCorrection L t)⁻¹
  have hy : Commute (y 1) (y t) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [CentralExtension.commutator_eq_of_image_eq f hk
      (exchange_image L 1).symm (exchange_image L t).symm]
    simpa only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, MulAut.conj_apply, inv_inv, z] using
      ((Commute.all (Multiplicative.ofAdd (1 : F)) (.ofAdd t)).map
        ((MulAut.conj z⁻¹).toMonoidHom.comp (L.shortRoot 1))).commutator_eq
  have hlong (i : Fin 3) (hi : i = 1 ∨ i = 2) (a : fixedField P) :
      Commute (L.longRoot i (.ofAdd a)) (y t) := by
    apply Commute.mul_right
    · exact (short_long L hc 1 i (by decide) t a).symm
    · apply Commute.inv_right
      exact (((short_long L hc 2 i (by decide) _ a).symm.mul_right
        (long_long L hc i 1 hi (Or.inl rfl) _ _)).mul_right
        (long_long L hc i 2 hi (Or.inr rfl) _ _))
  have hcorr1 : exchangeCorrection L 1 = L.longRoot 1 (.ofAdd 1) * L.longRoot 2 (.ofAdd 1) := by
    have ht : cubicTrace P 1 = 1 := cubicTrace_fixed P hP 1
    have hcoeff : higherCoefficient P 1 (1 : F) = 0 := by
      simp only [higherCoefficient, map_one, mul_one]
      exact CharTwo.add_self_eq_zero (1 : GaloisField 2 3)
    simp [exchangeCorrection, hcoeff, -fieldFrobenius_apply, ht]
  have h1 : Commute (L.shortRoot 1 (.ofAdd 1)) (y t) := by
    change Commute (L.shortRoot 1 (.ofAdd 1) * (exchangeCorrection L 1)⁻¹) (y t) at hy
    have hd : Commute (exchangeCorrection L 1)⁻¹ (y t) := by
      rw [hcorr1]
      exact ((hlong 1 (Or.inl rfl) 1).mul_left (hlong 2 (Or.inr rfl) 1)).inv_left
    exact (strip_right hy.symm hd.symm).symm
  have hcorr : Commute (L.shortRoot 1 (.ofAdd 1)) (exchangeCorrection L t) := by
    apply Commute.inv_right_iff.mp
    exact strip_left h1 ((Commute.all _ _).map _)
  have hshort := strip_right (strip_right hcorr
    (short_long L hc 1 2 (by decide) 1 _))
    (short_long L hc 1 1 (by decide) 1 _)
  have hh : higherCoefficient P 1 t = fieldFrobenius P t + t := by
    simp [higherCoefficient, -fieldFrobenius_apply]
  simpa only [pairing, hh] using hshort.commutator_eq
private theorem pairing_frobenius (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (L : RootSections 1 Nat.zero_lt_one f)
    (hc : CommutingPairs L) (x : F) :
    pairing L (fieldFrobenius P x) 1 = pairing L x 1 := by
  have hv := pairing_vanish hk L hc (fieldFrobenius P (fieldFrobenius P x))
  rw [pairing_reduce hf hk L, one_mul, map_add, fieldFrobenius_three,
    fieldFrobenius_three, pairing_add_left hk L hc] at hv
  have hx : pairing L x 1 * pairing L x 1 = 1 := by
    rw [← pairing_add_left hk L hc, CharTwo.add_self_eq_zero]
    simp [pairing]
  apply mul_right_cancel (b := pairing L x 1)
  exact hv.trans hx.symm

private theorem pairing_trace (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E) (L : RootSections 1 Nat.zero_lt_one f)
    (hc : CommutingPairs L) (x : F) :
    pairing L x 1 = pairing L (cubicTrace P x).val 1 := by
  rw [cubicTrace_coe, pairing_add_left hk L hc, pairing_add_left hk L hc,
    pairing_frobenius hf hk L hc, pairing_frobenius hf hk L hc,
    pairing_frobenius hf hk L hc, ← pairing_add_left hk L hc,
    CharTwo.add_self_eq_zero]
  simp [pairing]

/-- The highest short-pair formula holds in every central extension with the
specified additive sections and the ten commuting pairs. -/
theorem highestShortTrace (f : E →* G) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center E)
    (hcomm : CommutingPairs (initialRootSections f hf hk)) : HighestShortTrace f hf hk := by
  classical
  intro s t
  let L := initialRootSections f hf hk
  change pairing L s t = _
  rw [pairing_reduce hf hk, pairing_trace hf hk L hcomm, initialRootSections_long_two]
  rcases fixedField_cases (cubicTrace P (s * fieldFrobenius P t)) with h | h
  · rw [h]
    simp [pairing, binaryRootLift]
  · rw [h]
    change pairing L 1 1 = if (1 : fixedField P) = 0 then 1 else highestLift f hf hk
    rw [if_neg one_ne_zero]
    rfl

/-- The highest short-root trace identity for the canonical central cover,
with its original highest section. -/
theorem universal_highestShortTrace (hcomm : CommutingPairs universalRootSections) :
    HighestShortTrace (PerfectCentralCovering.universalProjection G)
      (PerfectCentralCovering.universalProjection_surjective G)
      (PerfectCentralCovering.universalProjection_ker_le_center G) :=
  highestShortTrace _ _ _ hcomm

end
end Triality.Standard.CentralCovers.TwoPrimary.SmallField.UpperShort
