module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.GroupDeductions
public import Theory.GroupTheory.PResidual.FrattiniGeneration
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Lifting the surviving minimal-parabolic quotient

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma 8.2.9, printed pp.720–721 (PDF pp.737–738).

Here `H` is the source minimal parabolic, considered intrinsically, and `T`
is its actual Sylow subgroup. All images use the literal map H → H/O₂(H).
The two-core normalizes V and its conjugate, hence I and O²(I). If I⁺
contains O²(H⁺), residual functoriality gives O²(H) = O²(I)(O²(H) ∩ O₂(H)).
Taking residuals removes this normalizing two-group supplement. Consequently
O²(I) = O²(H), H = IT as a set product, and T normalizes VA.

For the cyclic-three and cyclic-five alternatives, prime order and an odd
divisor of |I⁺| supply the quotient containment. The same lift contradicts
the nonnormalization assertion in 8.2.8(6) in the code branch.

These deductions do not establish the quotient alternatives. The odd-rank
argument and minimal-parabolic sieve, the U₃(4) exclusion, and the chief-section
and transvection exclusions remain with the assembly of 8.2.9. In particular
none of these proofs uses the inconsistent printed binary cocode tensor formula.
-/

public section
open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction
variable {H : Type*} [Group H]

/-- The two-core acts on the literal two-conjugate subgroup. Normality of
the two-core permits conjugating its action on V; normality of I is not assumed. -/
theorem twoCore_normalizes_twoConjugate (T : Sylow 2 H) (V : Subgroup H) (h : H)
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H)) :
    pCore 2 H ≤ normalizer
      ((V ⊔ V.map (MulAut.conj h⁻¹).toMonoidHom : Subgroup H) : Set H) := by
  apply normalizes_twoConjugate _ V h
    ((pCore_isPGroup.le_sylow_of_normal T).trans hTV)
  exact le_normalizer_of_normal (mem_top h)

variable [Finite H]

/-- Containment in the actual two-core quotient lifts to equality of the
embedded residuals. This proves the lifting step used in all surviving cases
of 8.2.9, without assuming normality of I or equality of the residuals. -/
theorem residual_eq_of_quotient_cover (T : Sylow 2 H) (V I : Subgroup H) (h : H)
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hgen : V ⊔ V.map (MulAut.conj h⁻¹).toMonoidHom = I)
    (hcover : pResidual 2 (H ⧸ pCore 2 H) ≤ I.map (QuotientGroup.mk' (pCore 2 H))) :
    (pResidual 2 I).map I.subtype = pResidual 2 H := by
  let R := (pResidual 2 I).map I.subtype
  let C := pResidual 2 H ⊓ pCore 2 H
  have hQI : pCore 2 H ≤ normalizer (I : Set H) := by
    rw [← hgen]
    exact twoCore_normalizes_twoConjugate T V h hTV
  have hQR : pCore 2 H ≤ normalizer (R : Set H) := hQI.trans
    (normalizer_le_normalizer_characteristic_image I (pResidual 2 I))
  have he : pResidual 2 H = R ⊔ C := by
    have hh := pResidual_eq_embedded_sup_kernel_of_map_le 2 I
      (QuotientGroup.mk' (pCore 2 H)) (by
        rwa [map_pResidual_of_surjective _ _ (QuotientGroup.mk'_surjective _)])
    simpa only [QuotientGroup.ker_mk'] using hh
  have hr := embedded_pResidual_join_pGroup R C
    (isPPerfect_embedded_pResidual 2 I)
    (pCore_isPGroup.to_le (show C ≤ pCore 2 H from inf_le_right))
    (inf_le_right.trans hQR)
  rw [← he, (pResidual_eq_top_iff 2 _).mpr (isPPerfect_pResidual 2),
    ← MonoidHom.range_eq_map, range_subtype] at hr
  exact hr.symm

/-- The precise consumer of the quotient cover: 8.2.9(1–2), including the
setwise product, from the two-conjugate and core-product conclusions of
8.2.2–8. The outstanding case analysis must still establish `hcover`. -/
theorem conclusions_of_quotient_cover (T : Sylow 2 H) (V I A : Subgroup H) (h : H)
    (hh : h ∈ I) (hTV : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hgen : V ⊔ V.map (MulAut.conj h⁻¹).toMonoidHom = I)
    (hP : A ⊔ (V ⊓ I.pCoreIn 2) = I.pCoreIn 2)
    (hcover : pResidual 2 (H ⧸ pCore 2 H) ≤ I.map (QuotientGroup.mk' (pCore 2 H))) :
    (pResidual 2 I).map I.subtype = pResidual 2 H ∧
      (T : Subgroup H) ≤ normalizer ((pResidual 2 I).map I.subtype : Set H) ∧
      (Set.univ : Set H) = (I : Set H) * (T : Set H) ∧
      (T : Subgroup H) ≤ normalizer ((V ⊔ A : Subgroup H) : Set H) := by
  have hr := residual_eq_of_quotient_cover T V I h hTV hgen hcover
  have hTR : (T : Subgroup H) ≤ normalizer ((pResidual 2 I).map I.subtype : Set H) := by
    rw [hr]
    exact le_normalizer_of_normal
  have hacts := offender_product_normalized I V A T h hh hgen hTV hTR hP
  have hRI : pResidual 2 H ≤ I := hr ▸ map_subtype_le _
  have hIT : I ⊔ (T : Subgroup H) = ⊤ := by
    apply top_unique
    rw [← pResidual_sup_sylow_eq_top T]
    exact sup_le_sup_right hRI _
  refine ⟨hr, hTR, ?_, hacts.2⟩
  change (Set.univ : Set H) = (I : Set H) * ((T : Subgroup H) : Set H)
  rw [← coe_mul_of_right_le_normalizer_left I (T : Subgroup H) hacts.1, hIT, coe_top]

/-- A prime-order two-residual lies in every subgroup which is not a
two-group. This supplies the cyclic-three and cyclic-five quotient cases. -/
theorem prime_residual_le (I : Subgroup H) (hprime : (Nat.card (pResidual 2 H)).Prime)
    (hI : ¬ IsPGroup 2 I) : pResidual 2 H ≤ I := by
  let R := pResidual 2 H
  let D := (pResidual 2 I).map I.subtype
  have hDR : D ≤ R := map_pResidual_le 2 I.subtype
  have hD : D ≠ ⊥ := by
    intro hb
    have hb' : pResidual 2 I = ⊥ := map_injective I.subtype_injective (by
      simpa only [Subgroup.map_bot] using hb)
    have hq : Function.Injective (QuotientGroup.mk' (pResidual 2 I)) :=
      (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hb'])
    exact hI ((isPGroup_quotient_pResidual 2).of_injective _ hq)
  let : Fact (Nat.card R).Prime := ⟨hprime⟩
  rcases (D.subgroupOf R).eq_bot_or_eq_top_of_prime_card with hb | ht
  · have hh := congrArg (map R.subtype) hb
    rw [map_subgroupOf_eq_of_le hDR, Subgroup.map_bot] at hh
    exact (hD hh).elim
  · exact (subgroupOf_eq_top.mp ht).trans (map_subtype_le _)

/-- An odd prime dividing |I⁺| forces the cover in either prime-order
residual case. Both the residual and I⁺ use H/O₂(H). -/
theorem quotient_cover_of_prime_residual (I : Subgroup H) {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2)
    (hprime : (Nat.card (pResidual 2 (H ⧸ pCore 2 H))).Prime)
    (hdiv : p ∣ Nat.card (I.map (QuotientGroup.mk' (pCore 2 H)))) :
    pResidual 2 (H ⧸ pCore 2 H) ≤ I.map (QuotientGroup.mk' (pCore 2 H)) := by
  apply prime_residual_le _ hprime
  intro hi
  obtain ⟨n, hn⟩ := hi.exists_card_eq
  rw [hn] at hdiv
  exact hodd ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow hdiv) |>.resolve_left hp.ne_one)

/-- The two prime-order branches of the source sieve already give the
normalizer conclusions. The odd divisor is taken in the actual I⁺, so an
abstract isomorphism to a small group must first be transported there. -/
theorem conclusions_of_prime_quotient_residual
    (T : Sylow 2 H) (V I A : Subgroup H) (h : H)
    (hh : h ∈ I) (hTV : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hgen : V ⊔ V.map (MulAut.conj h⁻¹).toMonoidHom = I)
    (hP : A ⊔ (V ⊓ I.pCoreIn 2) = I.pCoreIn 2)
    (horder : Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 3 ∨
      Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 5)
    (hdiv : 3 ∣ Nat.card (I.map (QuotientGroup.mk' (pCore 2 H))) ∨
      5 ∣ Nat.card (I.map (QuotientGroup.mk' (pCore 2 H)))) :
    (pResidual 2 I).map I.subtype = pResidual 2 H ∧
      (T : Subgroup H) ≤ normalizer ((pResidual 2 I).map I.subtype : Set H) ∧
      (Set.univ : Set H) = (I : Set H) * (T : Set H) ∧
      (T : Subgroup H) ≤ normalizer ((V ⊔ A : Subgroup H) : Set H) := by
  have hp : (Nat.card (pResidual 2 (H ⧸ pCore 2 H))).Prime := by
    rcases horder with he | he <;> rw [he] <;> decide
  apply conclusions_of_quotient_cover T V I A h hh hTV hgen hP
  rcases hdiv with hd | hd
  · exact quotient_cover_of_prime_residual I (by decide : Nat.Prime 3) (by decide) hp hd
  · exact quotient_cover_of_prime_residual I (by decide : Nat.Prime 5) (by decide) hp hd

/-- The contradiction with 8.2.8(6) after the code-case sieve has supplied
the actual quotient cover. No code-module label substitutes for its action. -/
theorem incompatible_with_code_obstruction (T : Sylow 2 H) (V I : Subgroup H) (h : H)
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hgen : V ⊔ V.map (MulAut.conj h⁻¹).toMonoidHom = I)
    (hcover : pResidual 2 (H ⧸ pCore 2 H) ≤ I.map (QuotientGroup.mk' (pCore 2 H)))
    (hcode : ¬ (T : Subgroup H) ≤ normalizer ((pResidual 2 I).map I.subtype : Set H)) :
    False := by
  apply hcode
  rw [residual_eq_of_quotient_cover T V I h hTV hgen hcover]
  exact le_normalizer_of_normal

end CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction
