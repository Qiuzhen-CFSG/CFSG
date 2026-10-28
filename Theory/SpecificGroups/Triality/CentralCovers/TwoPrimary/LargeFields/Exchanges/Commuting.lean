module
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Exchanges.LongRoots

/-!
# Commuting positive roots in normalized triality covers

All ten noninteracting pairs of normalized positive folded roots commute in
any surjective central extension of the genuine binary triality carrier.
The mixed pairs first commute in the carrier by the checked D₄ nonsum
relations. For a nonidentity fixed-field unit c, the actual arms and central
actors have short weights (c²,c⁻¹,c) and (c⁻¹,c,1). Their long weights are
(c⁻³,c³,1) and (c²,c⁻¹,c). These follow from the literal root-coroot pairings
and the fixed-field embedding into the cubic field.

The arms actor fixes the highest long root; the central actor fixes short
root 2. Products of arms and central actors at (c,c) and (c,c³) separate
the other pairs. Scalar-equivariant uniqueness then kills each central
defect. In characteristic two c² ≠ 1 whenever c ≠ 1, so the argument
includes the fixed field of order four without requiring c³ ≠ 1.
The two long-long pairs are supplied by `LongRoots`.

The applications give the literal positive-subgroup section and canonical
kernel exclusion, with only the four polynomial short-root exchanges left
as an explicit premise. Those equations must be supplied in the source
multiplier theorem's final assembly.

Sources: GLS3 2.4.5(b)(6), 2.4.7(f), and §6.1
(`refs/KGroup/GLS3/chapter2.tex`, `chapter6.tex`);
Aschbacher–Smith A.2.4 and I.1.3 (`refs/quasithin.pdf`, PDF pp.44 and 418).
-/

@[expose] public section
namespace Triality.Standard.CentralCovers.TwoPrimary
open Parabolics ConcreteBruhat RadicalCoordinates.LeviCommutators
open Theory.AlgebraicGroup.StandardRootSystem PositiveCoordinates
open Parabolics.RankOneMatrices PositiveCoordinates.SumExchangeData
noncomputable section
variable {n : ℕ} {hn : 0 < n} {E : Type*} [Group E]
variable {f : E →* BinaryCarrier n hn}
local notation "P" => binaryParameters n hn
namespace RootSections

private def shortWeights : Fin 3 → Fin 3 → Fin 4 → ℤ :=
  ![![![2,-1,0,0], ![0,-1,2,0], ![0,-1,0,2]],
    ![![1,1,-1,-1], ![-1,1,1,-1], ![-1,1,-1,1]],
    ![![1,0,1,-1], ![-1,0,1,1], ![1,0,-1,1]]]

private theorem short_pairing (i j : Fin 3) (k : Fin 4) :
    (typeDRootPairing 2).pairingIn ℤ (rootIndex (shortPosition i j))
      (typeDSimpleRootIndex 2 k) = shortWeights i j k := by
  have hd : (∑ l : Fin 4, rootCoords (simpleIndex k) l *
      rootCoords (positiveIndex (shortPosition i j)) l) = shortWeights i j k := by
    revert i j k
    decide +kernel
  apply Int.cast_injective (α := ℝ)
  change (algebraMap ℤ ℝ) _ = (shortWeights i j k : ℝ)
  rw [RootPairing.algebraMap_pairingIn, typeDRootPairing_pairing,
    ← rootEnumeration_positiveIndex, ← rootEnumeration_simpleIndex]
  change (∑ l : Fin 4, _ * _) = _
  simp only [← typeDRootPairing_root_val, rootCoords_spec]
  simpa only [Int.cast_sum, Int.cast_mul] using congrArg (fun z : ℤ => (z : ℝ)) hd

private theorem conj_product {G : Type*} [Group G] (a b x : G) :
    (a*b)*x*(a*b)⁻¹ = a*(b*x*b⁻¹)*a⁻¹ := by group

private theorem conj_mul {G : Type*} [Group G] (a x y : G) :
    a*(x*y)*a⁻¹ = (a*x*a⁻¹)*(a*y*a⁻¹) := by group

/-- The short-root weights of an arms actor from the actual fixed field. -/
def shortFixedArmsWeight (t : (fixedField P)ˣ) : Fin 3 → ExtensionField P :=
  ![t.val.val^2, t.val.val⁻¹, t.val.val]

/-- The short-root weights of the actual central actor. -/
def shortCentralWeight (t : (fixedField P)ˣ) : Fin 3 → ExtensionField P :=
  ![t.val.val⁻¹, t.val.val, 1]

private theorem fixed_arms_short (t : (fixedField P)ˣ) (i : Fin 3) (u : ExtensionField P) :
    elementaryInclusion P (torusElementary P rfl .arms (TorusCoordinates.fixedUnit P t)) *
      shortSplit P i u *
      (elementaryInclusion P (torusElementary P rfl .arms (TorusCoordinates.fixedUnit P t)))⁻¹ =
      shortSplit P i (shortFixedArmsWeight t i*u) := by
  have ht : fieldFrobenius P t.val.val = t.val.val := t.val.property
  have ht0 : t.val.val ≠ 0 := (TorusCoordinates.fixedUnit P t).ne_zero
  simp only [torusElementary_arms_val P rfl, TorusCoordinates.frobenius_fixedUnit,
    shortSplit, conj_mul, conj_product, torusWord_curve_conjugate P rfl, short_pairing]
  fin_cases i <;>
    simp [shortWeights, shortFixedArmsWeight, TorusCoordinates.fixedUnit,
      map_mul, map_pow, map_inv₀, ht, -fieldFrobenius_apply, ht0,
      mul_assoc, mul_comm, mul_left_comm]

private theorem central_short (t : (fixedField P)ˣ) (i : Fin 3) (u : ExtensionField P) :
    elementaryInclusion P (torusElementary P rfl .central t) * shortSplit P i u *
      (elementaryInclusion P (torusElementary P rfl .central t))⁻¹ =
      shortSplit P i (shortCentralWeight t i*u) := by
  have ht : fieldFrobenius P t.val.val = t.val.val := t.val.property
  simp only [torusElementary_central_val P rfl, shortSplit, conj_mul,
    torusWord_curve_conjugate P rfl, short_pairing]
  fin_cases i <;>
    simp [shortWeights, shortCentralWeight, TorusCoordinates.fixedUnit,
      map_mul, map_inv₀, ht, -fieldFrobenius_apply]

private theorem descend_short_scale (i : Fin 3) (a : Node) (t : (RootField P a)ˣ)
    (c : ExtensionField P)
    (h : ∀ u, elementaryInclusion P (torusElementary P rfl a t) * shortSplit P i u *
      (elementaryInclusion P (torusElementary P rfl a t))⁻¹ = shortSplit P i (c*u))
    (u : ExtensionField P) :
    torusActor P rfl a t * short P rfl i u * (torusActor P rfl a t)⁻¹ =
      short P rfl i (c*u) := by
  simp only [torusActor, short, ← map_mul, ← map_inv]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul, map_inv, shortElementary_val P rfl]
  exact h u

/-- The fixed-field arms actor scales each of the three normalized short roots. -/
theorem normalized_short_fixed_arms (L : RootSections n hn f) (hL : L.TorusNormalized)
    (t : (fixedField P)ˣ) (z : E)
    (hz : f z = torusActor P rfl .arms (TorusCoordinates.fixedUnit P t))
    (i : Fin 3) (u : ExtensionField P) :
    z * L.shortValue i u * z⁻¹ = L.shortValue i (shortFixedArmsWeight t i*u) := by
  apply hL.1 i .arms (TorusCoordinates.fixedUnit P t) (shortFixedArmsWeight t i) _ z hz u
  exact descend_short_scale i .arms (TorusCoordinates.fixedUnit P t) _ (fixed_arms_short t i)

/-- The central actor scales the first two short roots and fixes the third. -/
theorem normalized_short_central (L : RootSections n hn f) (hL : L.TorusNormalized)
    (t : (fixedField P)ˣ) (z : E) (hz : f z = torusActor P rfl .central t)
    (i : Fin 3) (u : ExtensionField P) :
    z * L.shortValue i u * z⁻¹ = L.shortValue i (shortCentralWeight t i*u) := by
  apply hL.1 i .central t (shortCentralWeight t i) _ z hz u
  exact descend_short_scale i .central t _ (central_short t i)

/-- The fixed-field arms actor has inverse-cube, cube, and trivial long weights. -/
theorem normalized_long_fixed_arms (L : RootSections n hn f) (hL : L.TorusNormalized)
    (t : (fixedField P)ˣ) (z : E)
    (hz : f z = torusActor P rfl .arms (TorusCoordinates.fixedUnit P t))
    (i : Fin 3) (u : fixedField P) :
    z * L.longValue i u * z⁻¹ = L.longValue i (![(t.val^3)⁻¹, t.val^3, 1] i*u) := by
  rw [L.normalized_long_arms hL _ z hz]
  have hN : cubicNorm P (TorusCoordinates.fixedUnit P t).val = t.val^3 := by
    apply Subtype.ext
    have ht : fieldFrobenius P t.val.val = t.val.val := t.val.property
    simp [cubicNorm, TorusCoordinates.fixedUnit, ht, -fieldFrobenius_apply, pow_succ]
  simp only [longArmsWeight, hN]
private theorem base_short_long_commute (i j : Fin 3) (hij : i ≠ 0 ∨ j ≠ 0)
    (s : ExtensionField P) (t : fixedField P) :
    Commute (short P rfl i s) (long P rfl j t) := by
  have h : Commute (shortElementary P rfl i s) (longElementary P rfl j t) := by
    apply Commute.of_map (elementaryInclusion_injective P)
    simp only [shortElementary_val P rfl, longElementary_val P rfl, shortSplit, longSplit]
    have hc (k : Fin 3) (u v : ExtensionField P) :
        Commute (curve P (shortPosition i k) u) (curve P (longPosition j) v) := by
      apply nonsumCommute_parameters P _ _
      · have he : ∀ i j k : Fin 3, shortPosition i k ≠ longPosition j := by decide +kernel
        exact he i j k
      · rintro ⟨l, hl⟩
        have hn : ∀ i j k : Fin 3, i ≠ 0 ∨ j ≠ 0 →
            ∀ l : Fin 12, (shortPosition i k, longPosition j, l) ∉ sumTriples := by
          decide +kernel
        exact hn i j k hij l ((mem_sumTriples_iff _ _ _).mpr ((root_sum_iff _ _ _).mp hl))
    exact ((hc 0 _ _).mul_left (hc 1 _ _)).mul_left (hc 2 _ _)
  exact h.map (toCarrier P)

/-- Every noninteracting pair of the six normalized positive roots commutes
in any surjective central extension, including for the fixed field of order four. -/
theorem normalized_commuting_relations (L : RootSections n hn f)
    (hL : L.TorusNormalized) (hlarge : 2 ≤ n)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    L.CommutingRelations := by
  have hq : 2 < (binaryParameters n hn).q := by
    change 2 < 2^n
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : 1 < n)
  obtain ⟨c, hc⟩ := exists_fixedUnit_ne_one P hq
  have hc0 : c.val ≠ 0 := c.ne_zero
  have hcE0 : c.val.val ≠ 0 := (TorusCoordinates.fixedUnit P c).ne_zero
  have hcE : c.val.val ≠ 1 := fun h => hc (Subtype.ext h)
  have hc2 : c.val^2 ≠ 1 := by
    intro h
    rcases sq_eq_one_iff.mp h with h | h
    · exact hc h
    · exact hc ((CharTwo.neg_eq (1 : fixedField P)) ▸ h)
  have hcE2 : c.val.val^2 ≠ 1 := by
    intro h
    rcases sq_eq_one_iff.mp h with h | h
    · exact hcE h
    · exact hcE ((CharTwo.neg_eq (1 : ExtensionField P)) ▸ h)
  obtain ⟨za, hza⟩ := hf (torusActor P rfl .arms (TorusCoordinates.fixedUnit P c))
  obtain ⟨zc, hzc⟩ := hf (torusActor P rfl .central c)
  obtain ⟨zc3, hzc3⟩ := hf (torusActor P rfl .central (c^3))
  have base (i j : Fin 3) (hij : i ≠ 0 ∨ j ≠ 0)
      (s : ExtensionField P) (t : fixedField P) :
      Commute (f (L.shortValue i s)) (f (L.longValue j t)) := by
    simpa only [shortValue, longValue, L.project_short, L.project_long] using
      base_short_long_commute i j hij s t
  -- Arms actors fix long root 2 and move every short root.
  have highest (i : Fin 3) (s : ExtensionField P) (t : fixedField P) :
      Commute (L.shortValue i s) (L.longValue 2 t) := by
    apply Commute.symm
    apply commute_of_scalar hk (L.shortRoot i) (L.longValue 2 t) za
      (shortFixedArmsWeight c i) _ _ _ _ s
    · fin_cases i
      · exact hcE2
      · exact inv_ne_one.mpr hcE
      · exact hcE
    · simpa using L.normalized_long_fixed_arms hL c za hza 2 t
    · intro u
      exact (base i 2 (Or.inr (by decide)) u t).symm
    · exact L.normalized_short_fixed_arms hL c za hza i
  -- Central actors fix short root 2 and move every long root.
  have upper (j : Fin 3) (s : ExtensionField P) (t : fixedField P) :
      Commute (L.shortValue 2 s) (L.longValue j t) := by
    apply commute_of_scalar hk (L.longRoot j) (L.shortValue 2 s) zc
      (longCentralWeight c j) _ _ _ _ t
    · fin_cases j
      · exact hc2
      · exact inv_ne_one.mpr hc
      · exact hc
    · simpa [shortCentralWeight] using L.normalized_short_central hL c zc hzc 2 s
    · exact base 2 j (Or.inl (by decide)) s
    · exact L.normalized_long_central hL c zc hzc j
  -- The product at (c,c) fixes short root 1 and moves long roots 0 and 1.
  have middle_fixed (s : ExtensionField P) :
      (za*zc)*L.shortValue 1 s*(za*zc)⁻¹ = L.shortValue 1 s := by
    rw [conj_product, L.normalized_short_central hL c zc hzc,
      L.normalized_short_fixed_arms hL c za hza]
    simp [shortFixedArmsWeight, shortCentralWeight, hcE0]
  have middle_long (j : Fin 3) (t : fixedField P) :
      (za*zc)*L.longValue j t*(za*zc)⁻¹ =
        L.longValue j (![c.val⁻¹,c.val^2,c.val] j*t) := by
    rw [conj_product, L.normalized_long_central hL c zc hzc,
      L.normalized_long_fixed_arms hL c za hza]
    congr 1
    fin_cases j <;> simp [longCentralWeight, pow_succ, hc0, mul_assoc, mul_comm, mul_left_comm]
  have middle (j : Fin 3) (s : ExtensionField P) (t : fixedField P) :
      Commute (L.shortValue 1 s) (L.longValue j t) := by
    apply commute_of_scalar hk (L.longRoot j) (L.shortValue 1 s) (za*zc)
      (![c.val⁻¹,c.val^2,c.val] j) _ (middle_fixed s) _ (middle_long j) t
    · fin_cases j
      · exact inv_ne_one.mpr hc
      · exact hc2
      · exact hc
    · exact base 1 j (Or.inl (by decide)) s
  -- The product at (c,c³) fixes long root 1 and moves short root 0 by c⁻¹.
  have lowest (s : ExtensionField P) (t : fixedField P) :
      Commute (L.shortValue 0 s) (L.longValue 1 t) := by
    apply Commute.symm
    apply commute_of_scalar hk (L.shortRoot 0) (L.longValue 1 t) (za*zc3)
      c.val.val⁻¹ (inv_ne_one.mpr hcE) _ _ _ s
    · rw [conj_product, L.normalized_long_central hL (c^3) zc3 hzc3,
        L.normalized_long_fixed_arms hL c za hza]
      simp [longCentralWeight, hc0]
    · intro u
      exact (base 0 1 (Or.inr (by decide)) u t).symm
    · intro u
      rw [conj_product, L.normalized_short_central hL (c^3) zc3 hzc3,
        L.normalized_short_fixed_arms hL c za hza]
      congr 1
      simp [shortFixedArmsWeight, shortCentralWeight, pow_succ, hcE0,
        mul_assoc, mul_comm, mul_left_comm]
  exact {
    short0_long1 := lowest
    short0_long2 := highest 0
    long0_short1 := fun s t => (middle 0 t s).symm
    long0_short2 := fun s t => (upper 0 t s).symm
    long0_long2 := L.normalized_long_commute_highest hL hlarge hf hk 0 (by decide)
    short1_long1 := middle 1
    short1_long2 := highest 1
    short2_long1 := upper 1
    short2_long2 := highest 2
    long1_long2 := L.normalized_long_commute_highest hL hlarge hf hk 1 (by decide) }

/-- After commuting pairs and the A₂ exchange are proved, only the four
polynomial short-root exchanges remain in the filtered collection contract. -/
theorem higherCommutators_of_normalized_short_exchanges
    (L : RootSections n hn f) (hL : L.TorusNormalized) (hlarge : 2 ≤ n)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hS : L.ShortExchangeRelations) : L.HigherCommutators :=
  L.higherCommutators_of_relations (L.normalized_commuting_relations hL hlarge hf hk)
    hS (L.normalized_long_exchange hL hlarge hf hk)

/-- Application to the literal positive subgroup and its original inclusion.
The independent short-exchange producer supplies exactly the remaining premise. -/
theorem exists_unipotent_section_of_normalized_short_exchanges
    (L : RootSections n hn f) (hL : L.TorusNormalized) (hlarge : 2 ≤ n)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (hS : L.ShortExchangeRelations) :
    ∃ s : unipotent P →* E, f.comp s = (unipotent P).subtype :=
  L.exists_unipotent_section
    (L.higherCommutators_of_normalized_short_exchanges hL hlarge hf hk hS)

end RootSections

/-- Canonical-kernel application: commuting relations are discharged, and
only the independently produced short-exchange equations are retained. -/
theorem universal_not_two_dvd_kernel_of_normalized_short_exchanges
    (n : ℕ) (hn : 0 < n) (hlarge : 2 ≤ n)
    (L : RootSections n hn (PerfectCentralCovering.universalProjection (BinaryCarrier n hn)))
    (hL : L.TorusNormalized) (hS : L.ShortExchangeRelations) :
    ¬ 2 ∣ Nat.card (PerfectCentralCovering.universalProjection (BinaryCarrier n hn)).ker :=
  universal_not_two_dvd_kernel_of_higherCommutators n hn L
    (L.higherCommutators_of_normalized_short_exchanges hL hlarge
      (PerfectCentralCovering.universalProjection_surjective _)
      (PerfectCentralCovering.universalProjection_ker_le_center _) hS)

end
end Triality.Standard.CentralCovers.TwoPrimary
