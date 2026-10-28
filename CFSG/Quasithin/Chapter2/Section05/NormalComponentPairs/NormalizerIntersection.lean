module
public import CFSG.Quasithin.Chapter2.Section05.NormalComponentPairs.NormalizerSource
/-!
# The original Sylow intersection of a largest-pair normalizer

Source 2.5.12(4) identifies the largest base as a Sylow subgroup of the
normalizer of any normal two-subgroup containing z. Its intersection with
the specified ambient Sylow T is therefore exactly that base. In particular,
an original crossing element in T outside S cannot normalize that subgroup.
This is the literal normalizer contradiction used in 2.5.15, pp.558--559.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup A6Shadow.Frattini ComponentRefinement
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass}
  {M H K U L Q : Subgroup G} {S : Sylow 2 H} {z x : G}

theorem largest_pair_normal_two_normalizer_intersection
    (c : MathieuSourceSetup H K M S z) (hG : IsSimpleQTKE κ G)
    (hp : (U,L) ∈ largestLocalPairs M H)
    (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (hQ : IsPGroup 2 Q) (hzQ : z ∈ Q) (hLN : L ≤ normalizer (Q : Set G)) :
    (c.T : Subgroup G) ⊓ normalizer (Q : Set G) = U := by
  obtain ⟨_,P,hP⟩ := largest_pair_normal_two_normalizer_of_source c hG hp hQ hzQ hLN
  let N := normalizer (Q : Set G)
  change (P : Subgroup N).map N.subtype = U at hP
  have hh : (c.T : Subgroup G).subgroupOf N = (P : Subgroup N) := by
    apply P.is_maximal' c.T.isPGroup'.comap_subtype
    intro y hy
    exact c.sylow_lt.le (hUS (hP ▸ mem_map_of_mem N.subtype hy))
  have he := congrArg (Subgroup.map N.subtype) hh
  simpa only [subgroupOf_map_subtype, hP] using he

theorem largest_pair_normal_two_not_normalized_by_crossing
    (c : MathieuSourceSetup H K M S z) (hG : IsSimpleQTKE κ G)
    (hp : (U,L) ∈ largestLocalPairs M H)
    (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (hQ : IsPGroup 2 Q) (hzQ : z ∈ Q) (hLN : L ≤ normalizer (Q : Set G))
    (hxT : x ∈ c.T) (hxS : x ∉ (S : Subgroup H).map H.subtype) :
    x ∉ normalizer (Q : Set G) := by
  intro hxN
  have hh := largest_pair_normal_two_normalizer_intersection c hG hp hUS hQ hzQ hLN
  exact hxS (hUS (hh ▸ (show x ∈ (c.T : Subgroup G) ⊓ normalizer (Q : Set G) from ⟨hxT,hxN⟩)))
end CFSG.Quasithin.Chapter2.Section05
