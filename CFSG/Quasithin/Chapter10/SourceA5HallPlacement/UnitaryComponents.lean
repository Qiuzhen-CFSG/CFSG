module
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.PerfectCore
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.NonnormalProjection

/-!
# The binary unitary-three component in the original odd normalizer

The actual fixed residual projects onto a perfect subgroup P of the
escaping component K, with noncentral two-core. A binary PSU₃ marking of
K/Z(K) kills O₂(P) in that quotient, so O₂(P) is central in K, a
contradiction. For nonnormal K the existing source outer-action theorem
supplies the required inner action of the same original residual.

Source: Aschbacher–Smith 4.4.9–11, printed p.621, including the SU₃(8)
central-cover row. No chosen-module cardinality or C.2.8 premise is used.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The binary unitary-three central quotient contradicts the actual perfect
projection with noncentral two-core in the original odd normalizer. -/
theorem source_oddNormalizer_no_binary_unitary_component
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    {f : ℕ} (hf : 0 < f) (hm : ClassicalGroup.IsPSU (K ⧸ center K) 3 (2 ^ f))
    (hinner : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K ⊔ centralizer (K : Set (normalizer (B : Set G)))) :
    False := by
  obtain ⟨P,Q,hPK,_,hP,_,_,_,hnc⟩ :=
    source_oddNormalizer_component_projection D B hBC hodd hBV K houtK hinner
  let := hP
  let j : P →* K ⧸ center K := (QuotientGroup.mk' (center K)).comp (inclusion hPK)
  have hk := ChapterF.Source.Unitary.perfect_hom_twoCore_le_ker hf hm j
  apply hnc
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rintro x ⟨u,hu,rfl⟩ y hy
  have hz : inclusion hPK u ∈ center K :=
    (QuotientGroup.eq_one_iff (inclusion hPK u)).mp (hk hu)
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y,hPK hy⟩)

/-- The actual nonnormal unitary-three component is excluded with its inner
residual action discharged from the original source configuration. -/
theorem source_oddNormalizer_no_binary_unitary_nonnormal_component
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (B : Subgroup G) [IsMulCommutative B] (hne : B ≠ ⊥)
    (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) (hnK : ¬ K.Normal)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    {f : ℕ} (hf : 0 < f) (hm : ClassicalGroup.IsPSU (K ⧸ center K) 3 (2 ^ f))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G)))) : False := by
  exact source_oddNormalizer_no_binary_unitary_component D B hBC hodd hBV K houtK hf hm
    (source_oddNormalizer_nonnormal_component_inner D B hne K hK hnK hFK)

end CFSG.Quasithin.Chapter10
