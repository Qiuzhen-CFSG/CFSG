module
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Exchanges.LongRoots

/-!
# Torus weights used in the short triality exchanges

Compute the coroot pairings in the actual twelve-root D₄ marking, then
transport the split diagonal actions through the elementary inclusion and
central quotient to the normalized sections. The fixed-field actors (c,c)
and (c²,c³) fix short root 1 and long root 0, respectively, and move short
root 0 by c. Thus a nonidentity unit suffices even over the field of order four.

Source: GLS3 §2.4.7(f), in the triality case of Aschbacher–Smith I.1.3.
-/

set_option linter.unusedSimpArgs false
@[expose] public section
namespace Triality.Standard.CentralCovers.TwoPrimary
open Parabolics ConcreteBruhat RadicalCoordinates.LeviCommutators
open Theory.AlgebraicGroup.StandardRootSystem PositiveCoordinates
open Parabolics.RankOneMatrices RadicalCoordinates.Centers PositiveCoordinates.SumExchangeData
noncomputable section
namespace RootSections.ShortPolynomial
variable {n : ℕ} {hn : 0 < n} {E : Type*} [Group E]
variable {f : E →* BinaryCarrier n hn}
local notation "P" => binaryParameters n hn

theorem conj_product {G : Type*} [Group G] (a b x : G) :
    (a*b)*x*(a*b)⁻¹ = a*(b*x*b⁻¹)*a⁻¹ := by group
theorem conj_mul {G : Type*} [Group G] (a x y : G) :
    a*(x*y)*a⁻¹ = (a*x*a⁻¹)*(a*y*a⁻¹) := by group
private def weights : Fin 12 → Fin 4 → ℤ :=
  ![![2,-1,0,0], ![0,-1,2,0], ![0,-1,0,2], ![-1,2,-1,-1],
    ![1,1,-1,-1], ![-1,1,1,-1], ![-1,1,-1,1],
    ![1,0,1,-1], ![-1,0,1,1], ![1,0,-1,1], ![1,-1,1,1], ![0,1,0,0]]
private theorem pairing (i : Fin 12) (j : Fin 4) :
    (typeDRootPairing 2).pairingIn ℤ (rootIndex i)
      (typeDSimpleRootIndex 2 j) = weights i j := by
  have hd : (∑ k : Fin 4, rootCoords (simpleIndex j) k *
      rootCoords (positiveIndex i) k) = weights i j := by
    revert i j
    decide +kernel
  apply Int.cast_injective (α := ℝ)
  change (algebraMap ℤ ℝ) _ = (weights i j : ℝ)
  rw [RootPairing.algebraMap_pairingIn, typeDRootPairing_pairing,
    ← rootEnumeration_positiveIndex, ← rootEnumeration_simpleIndex]
  change (∑ k : Fin 4, _ * _) = _
  simp only [← typeDRootPairing_root_val, rootCoords_spec]
  simpa only [Int.cast_sum, Int.cast_mul] using congrArg (fun z : ℤ => (z : ℝ)) hd

theorem short_arms (L : RootSections n hn f) (hL : L.TorusNormalized)
    (c : (fixedField P)ˣ) (z : E)
    (hz : f z = torusActor P rfl .arms (TorusCoordinates.fixedUnit P c))
    (i : Fin 3) (s : ExtensionField P) :
    z * L.shortValue i s * z⁻¹ = L.shortValue i ((![c.val.val^2,c.val.val⁻¹,c.val.val] i)*s) := by
  apply hL.1 i .arms (TorusCoordinates.fixedUnit P c) _ _ z hz s
  intro u
  simp only [baseShortHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
    torusActor, short, ← map_mul, ← map_inv]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul, map_inv, shortElementary_val P rfl, torusElementary_arms_val P rfl,
    conj_product, shortSplit, conj_mul, torusWord_curve_conjugate P rfl, pairing]
  have hc : fieldFrobenius P c.val.val = c.val.val := c.val.property
  have h0 : c.val.val ≠ 0 := fun h => c.ne_zero (Subtype.ext h)
  fin_cases i <;>
    simp [shortPosition, weights, TorusCoordinates.fixedUnit, TorusCoordinates.frobenius,
      hc, map_mul, map_inv₀, map_pow, -fieldFrobenius_apply, h0, pow_two, mul_assoc]

theorem short_central (L : RootSections n hn f) (hL : L.TorusNormalized)
    (c : (fixedField P)ˣ) (z : E) (hz : f z = torusActor P rfl .central c)
    (i : Fin 3) (s : ExtensionField P) :
    z * L.shortValue i s * z⁻¹ = L.shortValue i ((![c.val.val⁻¹,c.val.val,1] i)*s) := by
  apply hL.1 i .central c _ _ z hz s
  intro u
  simp only [baseShortHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
    torusActor, short, ← map_mul, ← map_inv]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul, map_inv, shortElementary_val P rfl, torusElementary_central_val P rfl,
    shortSplit, conj_mul, torusWord_curve_conjugate P rfl, pairing]
  have hc : fieldFrobenius P c.val.val = c.val.val := c.val.property
  fin_cases i <;>
    simp [shortPosition, weights, TorusCoordinates.fixedUnit,
      hc, map_mul, map_inv₀, -fieldFrobenius_apply]

theorem long_arms (L : RootSections n hn f) (hL : L.TorusNormalized)
    (c : (fixedField P)ˣ) (z : E)
    (hz : f z = torusActor P rfl .arms (TorusCoordinates.fixedUnit P c))
    (i : Fin 3) (s : fixedField P) :
    z * L.longValue i s * z⁻¹ = L.longValue i ((![(c.val^3)⁻¹,c.val^3,1] i)*s) := by
  rw [L.normalized_long_arms hL _ z hz]
  have hc : cubicNorm P (TorusCoordinates.fixedUnit P c).val = c.val^3 := by
    apply Subtype.ext
    have hc : fieldFrobenius P c.val.val = c.val.val := c.val.property
    simp [cubicNorm, TorusCoordinates.fixedUnit, hc, pow_succ, -fieldFrobenius_apply]
  simp only [longArmsWeight, hc]

theorem exists_unit (hlarge : 2 ≤ n) : ∃ c : (fixedField P)ˣ, c.val ≠ 1 := by
  apply exists_fixedUnit_ne_one
  change 2 < 2^n
  simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : 1 < n)

theorem actor (L : RootSections n hn f) (hL : L.TorusNormalized)
    (hf : Function.Surjective f) (a b : (fixedField P)ˣ) :
    ∃ z : E,
      (∀ i s, z*L.shortValue i s*z⁻¹ =
        L.shortValue i ((![a.val.val^2*b.val.val⁻¹,a.val.val⁻¹*b.val.val,a.val.val] i)*s)) ∧
      (∀ i s, z*L.longValue i s*z⁻¹ =
        L.longValue i ((![(a.val^3)⁻¹*b.val^2,a.val^3*b.val⁻¹,b.val] i)*s)) := by
  obtain ⟨za, hza⟩ := hf (torusActor P rfl .arms (TorusCoordinates.fixedUnit P a))
  obtain ⟨zb, hzb⟩ := hf (torusActor P rfl .central b)
  refine ⟨za*zb, ?_, ?_⟩
  · intro i s
    rw [conj_product, short_central L hL b zb hzb, short_arms L hL a za hza]
    fin_cases i <;> simp [mul_assoc]
  · intro i s
    rw [conj_product, L.normalized_long_central hL b zb hzb, long_arms L hL a za hza]
    fin_cases i <;> simp [longCentralWeight, mul_assoc]

theorem actor01 (L : RootSections n hn f) (hL : L.TorusNormalized)
    (hf : Function.Surjective f) (c : (fixedField P)ˣ) :
    ∃ z : E,
      (∀ i s, z*L.shortValue i s*z⁻¹ =
        L.shortValue i ((![c.val.val,1,c.val.val] i)*s)) ∧
      (∀ i s, z*L.longValue i s*z⁻¹ =
        L.longValue i ((![c.val⁻¹,c.val^2,c.val] i)*s)) := by
  obtain ⟨z, hs, hl⟩ := actor L hL hf c c
  have hc : c.val.val ≠ 0 := fun h => c.ne_zero (Subtype.ext h)
  refine ⟨z, ?_, ?_⟩
  · intro i s
    rw [hs]
    fin_cases i <;> simp [pow_succ, hc, mul_assoc, mul_comm, mul_left_comm]
  · intro i s
    rw [hl]
    fin_cases i <;> simp [pow_succ, c.ne_zero, mul_assoc, mul_comm, mul_left_comm]

theorem actor00 (L : RootSections n hn f) (hL : L.TorusNormalized)
    (hf : Function.Surjective f) (c : (fixedField P)ˣ) :
    ∃ z : E,
      (∀ i s, z*L.shortValue i s*z⁻¹ =
        L.shortValue i ((![c.val.val,c.val.val,c.val.val^2] i)*s)) ∧
      (∀ i s, z*L.longValue i s*z⁻¹ =
        L.longValue i ((![1,c.val^3,c.val^3] i)*s)) := by
  obtain ⟨z, hs, hl⟩ := actor L hL hf (c^2) (c^3)
  have hc : c.val.val ≠ 0 := fun h => c.ne_zero (Subtype.ext h)
  refine ⟨z, ?_, ?_⟩
  · intro i s
    rw [hs]
    fin_cases i <;> simp [pow_succ, hc, mul_assoc, mul_comm, mul_left_comm]
  · intro i s
    rw [hl]
    fin_cases i <;> simp [pow_succ, c.ne_zero, mul_assoc, mul_comm, mul_left_comm]
end RootSections.ShortPolynomial
end
end Triality.Standard.CentralCovers.TwoPrimary
