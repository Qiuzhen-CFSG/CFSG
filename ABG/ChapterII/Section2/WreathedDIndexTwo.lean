module
public import ABG.ChapterII.Section1.FusionPatterns
public import Theory.GroupTheory.CyclicSylowTwoOddOrder

/-!
# The wreathed D-pattern forces a normal subgroup of index two

For a finite group with an actual wreathed fusion frame, the D-pattern is
incompatible with having no normal subgroup of index two. The statement
retains the pattern's precise normal subgroup K and its Sylow subgroup whose
ambient image is U; no ambient index assumption on K is added.

Since U lies in S, the given Sylow subgroup of K lies in the restriction of
S to K. That restriction is a two-group, so Sylow maximality makes them equal.
Consequently K intersects S in U. The frame says U is maximal in the finite
two-group S, hence has index two. The image of S is therefore a Sylow subgroup
of G/K of order two. The no-index-two property descends to quotients, and
Burnside transfer would then give odd order for G/K, contradicting this
nontrivial Sylow image.

This supplies the obstruction to alternative (iii) of ABG Chapter II Section 1
Proposition 2, article p.11 of `refs/latex/alperin-brauer-gorenstein.tex`, used
in the no-index-two characterization of QD groups for Section 2 Proposition 2.
-/

namespace ABG
variable {G : Type*} [Group G] [Finite G]

/-- The wreathed D alternative entails a normal subgroup of index two. -/
public theorem WreathedDPattern.not_noNormalIndexTwo
    {S : Sylow 2 G} {n : ℕ} {U V : Subgroup G}
    (hD : WreathedDPattern U V) (hf : WreathedFusionFrame S n U V) :
    ¬ HasNoNormalIndexTwoSubgroup G := by
  intro hno
  obtain ⟨K, hKnormal, _, P, hPU⟩ := hD.1
  let := hKnormal
  have hPS : (P : Subgroup K) ≤ (S : Subgroup G).comap K.subtype := by
    intro x hx
    exact hf.2.1 (hPU ▸ Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hSP : (S : Subgroup G).comap K.subtype = (P : Subgroup K) :=
    P.is_maximal' S.isPGroup'.comap_subtype hPS
  have hKS : K.comap (S : Subgroup G).subtype = U.subgroupOf S := by
    ext x
    change (x : G) ∈ K ↔ (x : G) ∈ U
    constructor
    · intro hx
      have hp : (⟨x, hx⟩ : K) ∈ P := by
        change (⟨x, hx⟩ : K) ∈ (P : Subgroup K)
        rw [← hSP]
        exact x.property
      rw [← hPU]
      exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, hp, rfl⟩
    · intro hx
      rw [← hPU] at hx
      obtain ⟨y, _, hy⟩ := hx
      exact hy ▸ y.property
  have hindex : (K.comap (S : Subgroup G).subtype).index = 2 := by
    rw [hKS]
    exact S.isPGroup'.index_of_isCoatom _ hf.2.2.2.1
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  let R := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective K)
  have hcard : Nat.card R = 2 := by
    rw [Sylow.coe_mapSurjective, ← Subgroup.relIndex_ker _ q]
    rw [show q.ker = K from QuotientGroup.ker_mk' K]
    exact hindex
  have hnoQ : HasNoNormalIndexTwoSubgroup (G ⧸ K) := by
    intro L hL hi
    let := hL
    exact hno (L.comap q) inferInstance
      ((L.index_comap_of_surjective (QuotientGroup.mk'_surjective K)).trans hi)
  have hodd := odd_card_of_cyclic_sylow_two_of_no_normal_index_two R
    (isCyclic_of_prime_card hcard) hnoQ
  have hd : 2 ∣ Nat.card (G ⧸ K) := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card (R : Subgroup (G ⧸ K))
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd)
end ABG
