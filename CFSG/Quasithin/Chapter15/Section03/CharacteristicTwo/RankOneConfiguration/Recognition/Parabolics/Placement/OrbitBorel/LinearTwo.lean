module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.Reduction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.LinearTwo.OrbitCoordinates
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.LinearTwo.SolvableOvergroups

/-!
# The linear-two orbit Borel rank contradiction

The actual PSL₂(2ⁿ) component model supplies two-factor quotient coordinates
through `OrbitCoordinates`. Apply the solvable-overgroup calculation to
Y₊(S ∩ L₀). This puts Y₊ in the canonical Borel. The S-span
is S-invariant, so S normalizes both its Sylow intersection and its Borel;
Y₊ normalizes the Borel because it lies in it. Thus the constructed solvable
Borel is Y₊S-invariant. Its three-divisible order forces even n, and its two
matrix factors give three-rank greater than one, contradicting 15.3.26(3)
and the established rank bound for M_I.

The final exports construct the Borel and exclude the nonnormal linear-two
branch from its actual `ClassicalGroup.IsPSL` hypothesis. They discharge the
quotient coordinates and their Sylow alignment internally. The universal
earlier source results remain explicit, as do the rank-one and solvable
invariant conclusions of 15.3.26. Model selection and the other branches of
15.3.27 belong to the parent assembly. This route uses the invariant solvable
rank bound directly, without the intermediate equality M ∩ L₀ = B₀.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.27(1), printed p.1130 (PDF p.1147).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel.LinearTwo
variable {G : Type*} [Group G] [Finite G]
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem source_borel_witness_of_coordinates
    {K : GroupClass} (earlier : EarlierOrbitResults K) (hG : IsSimpleQTKE K G)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (hn : ¬ (c.L.subgroupOf I).Normal)
    (hS : Chapter1.IsSylowIn 2 d.S I) (h : RankOneFacts d I)
    (hr : primeRank 3 d.Yplus = 1)
    {n : ℕ} (hn₂ : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (a : Coordinates (localSpan c.L d.S) d.S F) :
    let B := canonicalBorel (localSpan c.L d.S) d.S
    B ≤ I ∧ d.Yplus ≤ B ∧ Group.IsSolvable B ∧
      d.Yplus ⊔ d.S ≤ normalizer (B : Set G) ∧
      Even n ∧ 1 < primeRank 3 B := by
  let L₀ := localSpan c.L d.S
  let B := canonicalBorel L₀ d.S
  have hLI := (orbit_normal_and_le d c hS
    (component_orbit_index_and_model earlier hG d hI c hn).1).1
  have hYL : d.Yplus ≤ L₀ := orbit_contains_yplus earlier hG d hI c hn hS h
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 4 = 2 ^ 2 from rfl).le.trans (Nat.pow_le_pow_right (by decide) hn₂)
  let H : Subgroup G := d.Yplus ⊔ (d.S ⊓ L₀)
  have hHY : H ≤ d.Yplus ⊔ d.S := sup_le le_sup_left (inf_le_left.trans le_sup_right)
  let := yplus_join_solvable d h
  have hsolH : Group.IsSolvable H :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hHY)
  have hYB : d.Yplus ≤ B := le_sup_left.trans
    (a.solvable_overgroup_le hfour H (sup_le hYL inf_le_right) le_sup_right hsolH)
  have hSN : d.S ≤ normalizer (B : Set G) :=
    canonicalBorel_normalized (le_normalizer_conjugateSpanBy c.L d.S)
      (sylow_normalizes_orbit_root d c)
  have hYSN : d.Yplus ⊔ d.S ≤ normalizer (B : Set G) :=
    sup_le (hYB.trans B.le_normalizer) hSN
  have hd : 3 ∣ Nat.card d.Yplus := by
    by_contra hnot
    have hz : primeRank 3 d.Yplus = 0 := PrimeRank.eq_zero_iff_not_dvd_card.mpr hnot
    omega
  have hb := a.borel_even_and_rank hF
    (hd.trans (card_dvd_of_injective (inclusion hYB) (inclusion_injective hYB)))
  exact ⟨(canonicalBorel_le _ _).trans hLI, hYB, a.borel_solvable hF, hYSN, hb⟩

theorem excluded_of_coordinates
    {K : GroupClass} (earlier : EarlierOrbitResults K) (hG : IsSimpleQTKE K G)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (hn : ¬ (c.L.subgroupOf I).Normal)
    (hS : Chapter1.IsSylowIn 2 d.S I) (h : RankOneFacts d I)
    (hr : primeRank 3 d.Yplus = 1) (hcontrol : SolvableInvariantControl d I)
    {n : ℕ} (hn₂ : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (a : Coordinates (localSpan c.L d.S) d.S F) : False := by
  obtain ⟨hBI, _, hs, hnB, _, hrB⟩ :=
    source_borel_witness_of_coordinates earlier hG d hI c hn hS h hr hn₂ hF a
  exact (not_lt_of_ge
    (invariant_solvable_three_rank_le_one d h hr hcontrol hBI hs hnB)) hrB

/-- Construct the source Borel from the actual intrinsic component model.
The field, characteristic, orbit quotient and root marking are all obtained
from the displayed hypotheses; no Borel conclusion is assumed. -/
theorem source_borel_witness_of_isPSL
    {K : GroupClass} (earlier : EarlierOrbitResults K) (hG : IsSimpleQTKE K G)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (hn : ¬ (c.L.subgroupOf I).Normal)
    (hS : Chapter1.IsSylowIn 2 d.S I) (h : RankOneFacts d I)
    (hr : primeRank 3 d.Yplus = 1)
    {n : ℕ} (hn₂ : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (c.L ⧸ pCore 2 c.L) 2 (2 ^ n)) :
    let B := canonicalBorel (localSpan c.L d.S) d.S
    B ≤ I ∧ d.Yplus ≤ B ∧ Group.IsSolvable B ∧
      d.Yplus ⊔ d.S ≤ normalizer (B : Set G) ∧
      Even n ∧ 1 < primeRank 3 B := by
  obtain ⟨F, hfield, hfinite, hF, ⟨e⟩⟩ := hm
  let _ := Fintype.ofFinite F
  let _ : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨a⟩ := linearTwo_orbit_coordinates earlier hG d hI c hn hS e
  exact source_borel_witness_of_coordinates earlier hG d hI c hn hS h hr hn₂ hF a

/-- The nonnormal linear-two branch of 15.3.27(1) is impossible.
The constructed solvable invariant Borel has three-rank greater than one,
contradicting the rank bound supplied by 15.3.26. -/
theorem excluded_of_isPSL
    {K : GroupClass} (earlier : EarlierOrbitResults K) (hG : IsSimpleQTKE K G)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (hn : ¬ (c.L.subgroupOf I).Normal)
    (hS : Chapter1.IsSylowIn 2 d.S I) (h : RankOneFacts d I)
    (hr : primeRank 3 d.Yplus = 1) (hcontrol : SolvableInvariantControl d I)
    {n : ℕ} (hn₂ : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (c.L ⧸ pCore 2 c.L) 2 (2 ^ n)) : False := by
  obtain ⟨hBI, _, hs, hnB, _, hrB⟩ :=
    source_borel_witness_of_isPSL earlier hG d hI c hn hS h hr hn₂ hm
  exact (not_lt_of_ge
    (invariant_solvable_three_rank_le_one d h hr hcontrol hBI hs hnB)) hrB

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel.LinearTwo
