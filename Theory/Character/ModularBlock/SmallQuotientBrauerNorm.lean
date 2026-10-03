module

public import Theory.Character.ModularBlock.SmallQuotientBrauerValues
public import Theory.GroupTheory.OddElementSum

/-!
# Normalized odd-element norms for the small principal Brauer families

The norm is the actual sum of squared complex norms over odd-order elements,
divided by the group order. Odd normal quotients preserve this sum; central
two-quotients divide it by the kernel order. Completeness and distinct simple
module degrees identify every supplied genuine family with the quotient models.

For a two-group quotient the singleton character is one and its scalar norm
is `b² / |G/N|`. For an odd normal quotient with a central subgroup of order
four and further quotient S₄, both simple characters are real on odd elements
and the norm, multiplied by 32, is `2u² + (u - 2w)²`. The computation counts
one identity and eight three-cycles in S₄ and uses the eigenvalue-defined
values `(1,2)` and `(1,-1)`. No ambient character expansion or Gram identity
is assumed.

Source: Fong, *Some Sylow subgroups of order 32*, J. Algebra 6 (1967),
printed pp. 71, 73–74.
-/

public section

noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
namespace ModularBlock.Cartan
open PrincipalBlockConstruction
variable {G : Type*} [Group G] [Finite G]

/-- The actual normalized squared norm, restricted to odd-order elements. -/
@[expose] def normalizedOddNorm (f : G → ℂ) : ℝ :=
  OddElementSum.normalized (fun g => Complex.normSq (f g))

/-- The norm is the group-order-normalized finite sum used in local contributions. -/
theorem normalizedOddNorm_eq (f : G → ℂ) :
    normalizedOddNorm f = (Nat.card G : ℝ)⁻¹ *
      ∑ g : G, if Odd (orderOf g) then Complex.normSq (f g) else 0 := rfl

/-- The genuine singleton family has scalar norm `b² / |G/N|`. -/
theorem normalizedOddNorm_of_oddNormal_twoGroup (d : PrincipalCongruenceBlockData G)
    (a : PrincipalBrauerFamily d 1) (N : Subgroup G) [N.Normal]
    (hN : Odd (Nat.card N)) (hQ : IsPGroup 2 (G ⧸ N))
    (hd : a.degree 0 = 1) (b : ℤ) :
    normalizedOddNorm (fun g => (b : ℂ) * BrauerCharacter.value d (a.rep 0) g) =
      (b : ℝ) ^ 2 / (Nat.card (G ⧸ N) : ℝ) := by
  calc
    _ = OddElementSum.normalized (fun _ : G => (b : ℝ) ^ 2) := by
      apply OddElementSum.normalized_congr
      intro g hg
      dsimp only
      rw [brauerValue_eq_one_of_oddNormal_twoGroup d a N hN hQ hd g hg, mul_one,
        Complex.normSq_intCast, pow_two]
    _ = OddElementSum.normalized (fun _ : G ⧸ N => (b : ℝ) ^ 2) :=
      OddElementSum.normalized_odd_quotient N hN (fun _ : G ⧸ N => (b : ℝ) ^ 2)
    _ = _ := by
      rw [OddElementSum.normalized_twoGroup hQ]
      rw [div_eq_mul_inv, mul_comm]

/-- Both degree-ordered genuine Brauer characters are real on odd-order elements. -/
theorem brauerValues_real_of_oddNormal_centralFour_symmetricFour
    (d : PrincipalCongruenceBlockData G) (a : PrincipalBrauerFamily d 2)
    (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N))
    (Z : Subgroup (G ⧸ N)) [Z.Normal]
    (hc : Z ≤ Subgroup.center (G ⧸ N)) (hcard : Nat.card Z = 4)
    (e : ((G ⧸ N) ⧸ Z) ≃* Equiv.Perm (Fin 4))
    (hd0 : a.degree 0 = 1) (hd1 : a.degree 1 = 2)
    (j : Fin 2) (g : G) (hg : Odd (orderOf g)) :
    (BrauerCharacter.value d (a.rep j) g).im = 0 := by
  obtain ⟨h0, h1⟩ := brauerValues_of_oddNormal_centralFour_symmetricFour
    d a N hN Z hc hcard e hd0 hd1 g hg
  fin_cases j
  · change (BrauerCharacter.value d (a.rep 0) g).im = 0
    rw [h0]
    rfl
  · change (BrauerCharacter.value d (a.rep 1) g).im = 0
    rw [h1]
    split_ifs <;> norm_num

open SymmetricFourConjugacy

private theorem odd_iff_cube (g : Equiv.Perm (Fin 4)) : Odd (orderOf g) ↔ g ^ 3 = 1 :=
  ⟨cube_eq_one_of_odd g, fun h => (by decide : Odd 3).of_dvd_nat
    (orderOf_dvd_iff_pow_eq_one.mpr h)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem card_three_cycles :
    (Finset.univ.filter (fun g : Equiv.Perm (Fin 4) => g ^ 3 = 1 ∧ g ≠ 1)).card = 8 := by
  decide

private theorem symmetricFour_sum (u w : ℤ) :
    (∑ g : Equiv.Perm (Fin 4), if Odd (orderOf g) then
      Complex.normSq ((u : ℂ) + (w : ℂ) * (if g = 1 then 2 else -1)) else 0) =
      (u + 2 * w : ℝ) ^ 2 + 8 * (u - w : ℝ) ^ 2 := by
  classical
  have hv (g : Equiv.Perm (Fin 4)) :
      (if Odd (orderOf g) then
        Complex.normSq ((u : ℂ) + (w : ℂ) * (if g = 1 then 2 else -1)) else 0) =
      (if g = 1 then (u + 2 * w : ℝ) ^ 2 else 0) +
      (if g ^ 3 = 1 ∧ g ≠ 1 then (u - w : ℝ) ^ 2 else 0) := by
    simp only [odd_iff_cube]
    by_cases h : g = 1
    · subst g
      simp [Complex.normSq_apply]
      ring
    · by_cases h3 : g ^ 3 = 1
      · simp [h, h3, Complex.normSq_apply]
        ring
      · simp [h, h3]
  simp_rw [hv]
  rw [Finset.sum_add_distrib]
  have hs : (∑ g : Equiv.Perm (Fin 4),
      if g ^ 3 = 1 ∧ g ≠ 1 then (u - w : ℝ) ^ 2 else 0) = 8 * (u - w : ℝ) ^ 2 := by
    rw [← Finset.sum_filter, Finset.sum_const, card_three_cycles]
    simp
  rw [hs]
  simp

/-- The actual normalized odd-element sum through the two successive quotients. -/
theorem normalizedOddNorm_of_oddNormal_centralFour_symmetricFour
    (d : PrincipalCongruenceBlockData G) (a : PrincipalBrauerFamily d 2)
    (N : Subgroup G) [N.Normal] (hN : Odd (Nat.card N))
    (Z : Subgroup (G ⧸ N)) [Z.Normal]
    (hc : Z ≤ Subgroup.center (G ⧸ N)) (hcard : Nat.card Z = 4)
    (e : ((G ⧸ N) ⧸ Z) ≃* Equiv.Perm (Fin 4))
    (hd0 : a.degree 0 = 1) (hd1 : a.degree 1 = 2) (u w : ℤ) :
    32 * normalizedOddNorm (fun g =>
      (u : ℂ) * BrauerCharacter.value d (a.rep 0) g +
      (w : ℂ) * BrauerCharacter.value d (a.rep 1) g) =
      ((2 * u ^ 2 + (u - 2 * w) ^ 2 : ℤ) : ℝ) := by
  classical
  let f : Equiv.Perm (Fin 4) → ℝ := fun g =>
    Complex.normSq ((u : ℂ) + (w : ℂ) * (if g = 1 then 2 else -1))
  have hn : normalizedOddNorm (fun g =>
      (u : ℂ) * BrauerCharacter.value d (a.rep 0) g +
      (w : ℂ) * BrauerCharacter.value d (a.rep 1) g) =
      (4 : ℝ)⁻¹ * OddElementSum.normalized f := by
    calc
      _ = OddElementSum.normalized (fun g : G =>
          f (e (QuotientGroup.mk' Z (QuotientGroup.mk' N g)))) := by
        apply OddElementSum.normalized_congr
        intro g hg
        obtain ⟨h0, h1⟩ := brauerValues_of_oddNormal_centralFour_symmetricFour
          d a N hN Z hc hcard e hd0 hd1 g hg
        dsimp only
        rw [h0, h1, mul_one]
      _ = OddElementSum.normalized (fun q : G ⧸ N =>
          f (e (QuotientGroup.mk' Z q))) :=
        OddElementSum.normalized_odd_quotient N hN
          (fun q : G ⧸ N => f (e (QuotientGroup.mk' Z q)))
      _ = (Nat.card Z : ℝ)⁻¹ * OddElementSum.normalized (fun q => f (e q)) :=
        OddElementSum.normalized_central_two_quotient Z hc
          (IsPGroup.of_card (n := 2) (by simpa using hcard)) (fun q => f (e q))
      _ = _ := by rw [hcard, OddElementSum.normalized_equiv e f]; norm_num
  have hs : OddElementSum.normalized f =
      (24 : ℝ)⁻¹ * ((u + 2 * w : ℝ) ^ 2 + 8 * (u - w : ℝ) ^ 2) := by
    unfold OddElementSum.normalized
    have horder : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    rw [horder]
    congr 1
    convert symmetricFour_sum u w using 1
    congr 2
    exact Subsingleton.elim _ _
  rw [hn, hs]
  push_cast
  ring

end ModularBlock.Cartan
