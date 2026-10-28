module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.RankOne
public import Theory.GroupTheory.PResidual.PrimeToMonotone

/-!
# Residual and Sylow reductions for component placement

A normal subgroup whose intersection with M_I has order divisible by three
contains Y₊: its intersection contains a Sylow three-subgroup of M_I, since
these Sylow subgroups have order at most three. Its normality then gives
containment of the prime-to-three residual. Solvable-invariant control
supplies the required intersection for the inner-projection argument.

The remaining lemmas implement the Borel equality and rank contradiction,
and transport the nonnormal orbit's residual identity. They do not construct
that orbit or classify its components.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.27, printed pp.1130–1131 (PDF pp.1147–1148).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement
variable {G : Type*} [Group G] [Finite G]

/-- A normal subgroup meeting the intersection in three-divisible order contains
its prime-to-three residual, since every Sylow three-subgroup has order at most three. -/
theorem yplus_le_of_normal_three_divisor
    (d : LocalData G) {I N : Subgroup G} (h : RankOneFacts d I)
    (hn : (N.subgroupOf (d.MI I)).Normal)
    (hd : 3 ∣ Nat.card (N.subgroupOf (d.MI I))) : d.Yplus ≤ N := by
  let A := N.subgroupOf (d.MI I)
  let : A.Normal := hn
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 hd
  let Q := (zpowers x).map A.subtype
  have hc : Nat.card Q = 3 := by
    rw [card_map_of_injective A.subtype_injective, Nat.card_zpowers, hx]
  have hp : IsPGroup 3 Q := IsPGroup.of_card (hc.trans (pow_one 3).symm)
  obtain ⟨P, hQP⟩ := hp.exists_le_sylow
  have he : Q = (P : Subgroup (d.MI I)) :=
    eq_of_le_of_card_ge hQP ((intersection_sylow_three_card_le_three d h P).trans hc.ge)
  have hPA : (P : Subgroup (d.MI I)) ≤ A := he ▸ map_subtype_le (zpowers x)
  have hres : primeToResidual 3 (d.MI I) ≤ A := primeToResidual_le A
    ((Nat.prime_three.coprime_iff_not_dvd.mpr P.not_dvd_index).coprime_dvd_right
      (index_dvd_of_le hPA))
  rw [h.residual]
  rintro _ ⟨m, hm, rfl⟩
  exact hres hm

/-- The invariant solvable preimage inside the component supplies containment.
Its three-divisible order is enough; no whole-star-kernel assumption is used. -/
theorem yplus_le_component_of_invariant_solvable
    (d : LocalData G) {I X : Subgroup G}
    (c : ComponentWitness d I) (h : RankOneFacts d I)
    (hcontrol : SolvableInvariantControl d I)
    (hn : (c.L.subgroupOf I).Normal)
    (hXL : X ≤ c.L) (hs : Group.IsSolvable X)
    (hXn : d.Yplus ⊔ d.S ≤ normalizer (X : Set G))
    (hd : 3 ∣ Nat.card X) : d.Yplus ≤ c.L := by
  have hXM := hcontrol X (hXL.trans (component_le c)) hs hXn
  have hIL := (normal_subgroupOf_iff_le_normalizer (component_le c)).mp hn
  apply yplus_le_of_normal_three_divisor d h
    (normal_subgroupOf_of_le_normalizer (inf_le_right.trans hIL))
  let f : X →* c.L.subgroupOf (d.MI I) :=
    (inclusion hXM).codRestrict _ (fun x => hXL x.property)
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext (congrArg (fun x : c.L.subgroupOf (d.MI I) => (x : G)) he)
  exact hd.trans (card_dvd_of_injective f hf)

omit [Finite G] in
/-- The theta alternative of the model comparison gives containment using
the exact earlier conclusion 15.3.11(6). -/
theorem yplus_le_of_theta
    (d : LocalData G) {I L : Subgroup G}
    (h6 : theta (d.MI I) = d.Yplus) (hL : theta I ≤ L) : d.Yplus ≤ L := by
  rw [← h6]
  exact (theta_mono inf_le_right).trans hL
omit [Finite G] in
/-- The nonnormal orbit's genuine `O^{3'}` identity contains `Y₊` by
monotonicity of that residual, without replacing it by a two-residual. -/
theorem yplus_le_orbit_of_residual
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (h : RankOneFacts d I)
    (hres : (primeToResidual 3 I).map I.subtype = localSpan c.L d.S) :
    d.Yplus ≤ localSpan c.L d.S := by
  rw [h.residual]
  exact (embedded_primeToResidual_mono 3 inf_le_right).trans_eq hres

omit [Finite G] in
/-- Solvable-invariant control identifies the Borel with `M ∩ L₀`,
once the model argument supplies the Borel and the opposite containment. -/
theorem orbit_borel_eq_intersection
    (d : LocalData G) {I L₀ B : Subgroup G}
    (hcontrol : SolvableInvariantControl d I)
    (hL₀ : L₀ ≤ I) (hB : B ≤ L₀) (hMB : d.M ⊓ L₀ ≤ B)
    (hs : Group.IsSolvable B)
    (hn : d.Yplus ⊔ d.S ≤ normalizer (B : Set G)) : B = d.M ⊓ L₀ := by
  exact le_antisymm (le_inf ((hcontrol B (hB.trans hL₀) hs hn).trans inf_le_left) hB) hMB

/-- The source Borel-rank contradiction: every solvable invariant subgroup
of I has three-rank at most one. The nonnormal model branch must construct
its Borel of larger rank to contradict this bound. -/
theorem invariant_solvable_three_rank_le_one
    (d : LocalData G) {I B : Subgroup G}
    (h : RankOneFacts d I) (hr : primeRank 3 d.Yplus = 1)
    (hcontrol : SolvableInvariantControl d I)
    (hBI : B ≤ I) (hs : Group.IsSolvable B)
    (hn : d.Yplus ⊔ d.S ≤ normalizer (B : Set G)) : primeRank 3 B ≤ 1 := by
  have hBM := hcontrol B hBI hs hn
  exact (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hBM)
    (inclusion_injective hBM)).trans (intersection_three_rank_le_one d h hr)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement
