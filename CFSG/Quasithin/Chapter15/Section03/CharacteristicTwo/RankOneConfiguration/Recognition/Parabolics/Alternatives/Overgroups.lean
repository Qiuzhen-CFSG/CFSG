module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.RankOne

/-!
# Three-rank bounds for proper overgroups in the star quotient

The preimage in I of a proper subgroup of I* containing (Y₊S)* is a
proper overgroup of Y₊S. Minimality of I puts this preimage in M ∩ I.
The odd rank-one Sylow theorem makes the Sylow three-subgroups of M ∩ I
cyclic, and this property passes to its actual star image. Hence every
such proper overgroup has three-rank at most one.

This is the ambient contradiction used for both partition stabilizers in
the A₇ branch. The existence of a partition-stabilizer overgroup of rank
two is a separate model calculation; it is not assumed to be proved here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.27(4) and 15.3.28, printed p.1131 (PDF p.1148).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics
variable {G : Type*} [Group G]

/-- Every proper overgroup of (Y₊S)* lies in the actual intersection image. -/
theorem proper_star_overgroup_le_intersection [Finite G]
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.HplusMinimal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (H : Subgroup (d.Star I))
    (hYH : d.starImage I (d.Yplus ⊔ d.S) ≤ H) (hH : H ≠ ⊤) :
    H ≤ d.starImage I (d.MI I) := by
  let J := (H.comap (d.starMap I)).map I.subtype
  have hJI : J ≤ I := map_subtype_le _
  have hYJ : d.Yplus ⊔ d.S ≤ J := by
    intro y hy
    refine mem_map.mpr ⟨⟨y, hI.1.1.2 hy⟩, ?_, rfl⟩
    exact hYH (mem_map.mpr ⟨⟨y, hI.1.1.2 hy⟩, hy, rfl⟩)
  have hlt : J < I := lt_of_le_of_ne hJI (by
    intro he
    apply hH
    apply top_unique
    intro z _
    obtain ⟨i, rfl⟩ := QuotientGroup.mk'_surjective (localActionKernel d.Z I) z
    have hi : (i : G) ∈ J := he.ge i.property
    obtain ⟨j, hj, hji⟩ := hi
    have heq : j = i := Subtype.ext hji
    exact heq ▸ hj)
  have hJM := proper_overgroup_le_intersection d hI P hP hYJ hlt
  intro z hz
  obtain ⟨i, rfl⟩ := QuotientGroup.mk'_surjective (localActionKernel d.Z I) z
  exact mem_map.mpr ⟨i, hJM (mem_map.mpr ⟨i, hz, rfl⟩), rfl⟩

/-- The three-rank-one bound passes to the actual star image by cyclic Sylow transport. -/
theorem intersection_star_three_rank_le_one [Finite G]
    (d : LocalData G) {I : Subgroup G} (h : RankOneFacts d I)
    (hr : primeRank 3 d.Yplus = 1) :
    primeRank 3 (d.starImage I (d.MI I)) ≤ 1 := by
  let f : d.MI I →* d.Star I := (d.starMap I).comp (inclusion inf_le_right)
  have hf : f.range = d.starImage I (d.MI I) := by
    rw [MonoidHom.range_comp, inclusion_range]
    rfl
  let Q : Sylow 3 (d.MI I) := Sylow.nonempty.some
  have hQ : IsCyclic Q := Q.isCyclic_of_odd_of_primeRank_le_one (by decide)
    (intersection_three_rank_le_one d h hr)
  rw [← hf]
  exact Q.primeRank_le_one_of_surjective hQ f.rangeRestrict f.rangeRestrict_surjective

/-- The rank bound applies to every proper overgroup, without a kernel-containment assumption. -/
theorem proper_star_overgroup_three_rank_le_one [Finite G]
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.HplusMinimal)
    (h : RankOneFacts d I) (hr : primeRank 3 d.Yplus = 1)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (H : Subgroup (d.Star I))
    (hYH : d.starImage I (d.Yplus ⊔ d.S) ≤ H) (hH : H ≠ ⊤) :
    primeRank 3 H ≤ 1 := by
  have hle := proper_star_overgroup_le_intersection d hI P hP H hYH hH
  exact (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hle)
    (inclusion_injective hle)).trans (intersection_star_three_rank_le_one d h hr)

/-- A proper overgroup of (Y₊S)* with three-rank at least two gives a contradiction. -/
theorem no_proper_star_overgroup_of_three_rank_two [Finite G]
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.HplusMinimal)
    (h : RankOneFacts d I) (hr : primeRank 3 d.Yplus = 1)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (H : Subgroup (d.Star I))
    (hYH : d.starImage I (d.Yplus ⊔ d.S) ≤ H) (hH : H ≠ ⊤)
    (hlarge : 2 ≤ primeRank 3 H) : False := by
  have hb := proper_star_overgroup_three_rank_le_one d hI h hr P hP H hYH hH
  omega

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics
