module
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.CharP.Basic

/-!
# Faithfulness of coordinate groups in a central quotient

Suppose actors invert one coordinate at a time in a marked product map.
If an image is central, comparing it with each conjugate isolates the square
of that coordinate. Individual coordinate faithfulness and absence of
involutions then force every coordinate to be trivial. Thus the literal
center projection remains injective on the entire product.

The dependent-field specialization applies to odd-characteristic root charts,
and the final four-coordinate application gives the defining-prime rank
bound in the actual central quotient. The E₆/E₇/E₈ source owners construct
the root curves and coroot actors supplying these hypotheses.
Source: the higher exceptional exclusions in Aschbacher–Smith A.2.17,
printed p.39; elementary root and coroot actions in GLS3 §2.3.
-/

namespace CoordinateInversion
variable {I : Type*} [DecidableEq I] {A : I → Type*} [∀ i, CommGroup (A i)]
  {H : Type*} [Group H]

@[expose] public def invertCoordinate (i : I) (a : ∀ i, A i) : ∀ k, A k :=
  fun k => if k = i then (a k)⁻¹ else a k

public theorem center_iff
    (h2 : ∀ i (x : A i), x^2=1 → x=1)
    (j : (∀ i, A i) →* H)
    (hi : ∀ i, Function.Injective (fun x : A i => j (Pi.mulSingle i x)))
    (d : I → H)
    (hd : ∀ i a, d i * j a * (d i)⁻¹ = j (invertCoordinate i a))
    (a : ∀ i, A i) : j a ∈ Subgroup.center H ↔ a = 1 := by
  constructor
  · intro hc
    funext i
    have he : j (invertCoordinate i a) = j a := by
      rw [← hd, (Subgroup.mem_center_iff.mp hc (d i)), mul_assoc,
        mul_inv_cancel, mul_one]
    have hv : a⁻¹ * invertCoordinate i a = Pi.mulSingle i ((a i)⁻¹ * (a i)⁻¹) := by
      funext k
      by_cases hk : k = i
      · subst k
        simp [invertCoordinate]
      · simp [invertCoordinate, hk]
    have hi1 : (a i)⁻¹ * (a i)⁻¹ = 1 := by
      apply hi i
      change j (Pi.mulSingle i ((a i)⁻¹ * (a i)⁻¹)) = j (Pi.mulSingle i 1)
      rw [← hv, map_mul, map_inv, he]
      simp
    exact inv_eq_one.mp (h2 i _ (by simpa only [pow_two] using hi1))
  · rintro rfl
    simp

public theorem quotient_injective
    (h2 : ∀ i (x : A i), x^2=1 → x=1)
    (j : (∀ i, A i) →* H)
    (hi : ∀ i, Function.Injective (fun x : A i => j (Pi.mulSingle i x)))
    (d : I → H)
    (hd : ∀ i a, d i * j a * (d i)⁻¹ = j (invertCoordinate i a)) :
    Function.Injective ((QuotientGroup.mk' (Subgroup.center H)).comp j) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  exact (center_iff h2 j hi d hd a).mp ((QuotientGroup.eq_one_iff (j a)).mp ha)

public theorem field_quotient_injective
    {F : I → Type*} [∀ i, Field (F i)] (h2 : ∀ i, (2 : F i) ≠ 0)
    (j : (∀ i, Multiplicative (F i)) →* H)
    (hi : ∀ i, Function.Injective (fun x : Multiplicative (F i) => j (Pi.mulSingle i x)))
    (d : I → H)
    (hd : ∀ i a, d i * j a * (d i)⁻¹ = j (invertCoordinate i a)) :
    Function.Injective ((QuotientGroup.mk' (Subgroup.center H)).comp j) := by
  apply quotient_injective _ j hi d hd
  intro i x hx
  change (2:ℕ) • x.toAdd = 0 at hx
  change x.toAdd = 0
  exact (mul_eq_zero.mp (by simpa [nsmul_eq_mul] using hx)).resolve_left (h2 i)

public theorem four_mul_fieldExponent_le_primeRank_centerQuotient
    {F : Type*} [Field F] [Finite F] [Finite H]
    {p e : ℕ} [Fact p.Prime] [CharP F p]
    (h2 : (2:F) ≠ 0) (hcard : Nat.card F = p^e)
    (j : (Fin 4 → Multiplicative F) →* H)
    (hi : ∀ i, Function.Injective (fun x : Multiplicative F => j (Pi.mulSingle i x)))
    (d : Fin 4 → H)
    (hd : ∀ i a, d i * j a * (d i)⁻¹ = j (invertCoordinate i a)) :
    4*e ≤ primeRank p (H ⧸ Subgroup.center H) := by
  apply primeRank_ge_of_elementary_embedding (A := Fin 4 → Multiplicative F)
    (p := p) (f := (QuotientGroup.mk' (Subgroup.center H)).comp j)
  · intro a
    funext i
    change p • (a i).toAdd = 0
    simp [nsmul_eq_mul]
  · simp only [Nat.card_fun, Nat.card_fin, Nat.card_congr Multiplicative.toAdd]
    rw [hcard, ← pow_mul, mul_comm e 4]
  · exact field_quotient_injective (fun _ => h2) j hi d hd
end CoordinateInversion
