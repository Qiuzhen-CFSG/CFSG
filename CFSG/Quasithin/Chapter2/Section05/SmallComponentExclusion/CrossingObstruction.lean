module
public import CFSG.Quasithin.Chapter2.Section05.NormalComponentPairs.NormalizerIntersection
public import CFSG.Quasithin.Chapter2.Section05.NormalComponentPairs.CoreSource
public import Theory.GroupTheory.CentralizerKernelNormalizer

/-!
# The crossing normalizer obstruction in the small-component exclusion

If an original outside Sylow-normalizer element centralizes R, it normalizes
any subgroup Q of S that normalizes R and contains C_S(R). When Q is the
normal two-core of a largest local pair and contains z, source 2.5.12(4)
forbids this: its normalizer intersects T in the base U≤S.
The direct-product branch Q=O₂(H)E uses precisely this argument in 2.5.15.
The earlier producer must supply the actual R and centralizing crossing;
no component-normalization hypothesis on that crossing is imposed.
Source: Aschbacher--Smith 2.5.15, printed p.559.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory A6Shadow.Frattini ComponentRefinement ComponentSelection
open ClassificationModels
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass}
  {H K M U L Q R E : Subgroup G} {S : Sylow 2 H} {z x : G}

/-- The source normalizer contradiction, using the actual crossing and local core. -/
theorem crossing_normal_two_false
    (c : MathieuSourceSetup H K M S z) (hG : IsSimpleQTKE κ G)
    (hp : (U,L) ∈ largestLocalPairs M H)
    (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (hQ : IsPGroup 2 Q) (hzQ : z ∈ Q) (hLN : L ≤ normalizer (Q : Set G))
    (hQS : Q ≤ (S : Subgroup H).map H.subtype) (hQR : Q ≤ normalizer (R : Set G))
    (hCR : (S : Subgroup H).map H.subtype ⊓ centralizer (R : Set G) ≤ Q)
    (hxT : x ∈ c.T) (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (hxN : x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G))
    (hxR : x ∈ centralizer (R : Set G)) : False := by
  exact largest_pair_normal_two_not_normalized_by_crossing c hG hp hUS hQ hzQ hLN hxT hxS
    (mem_normalizer_of_centralizes_action_kernel hQS hQR hCR hxN hxR)

/-- The original four-normalizer core cannot contain the crossing's entire
centralizer in S while itself normalizing the marked residual. -/
theorem crossing_four_normalizer_core_false
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype) (hb : ¬ IsBenderModel K)
    (hp : (U,L) ∈ largestLocalPairs M H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    [IsKleinFour E] (hES : E ≤ (S : Subgroup H).map H.subtype) (hEK : E ≤ K)
    (hL : L = H ⊓ normalizer (E : Set G))
    (hzE : z ∈ centralizer (E : Set G))
    (hQR : (S : Subgroup H).map H.subtype ⊓ centralizer (E : Set G) ≤ normalizer (R : Set G))
    (hCR : (S : Subgroup H).map H.subtype ⊓ centralizer (R : Set G) ≤ centralizer (E : Set G))
    (hxT : x ∈ c.T) (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (hxN : x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G))
    (hxR : x ∈ centralizer (R : Set G)) : False := by
  have hcore := four_normalizer_twoCore_of_source c hG hempty hgen hb hES hEK
  rw [← hL] at hcore
  have hzS : z ∈ (S : Subgroup H).map H.subtype := c.center_le c.mem_center
  have hzQ : z ∈ twoCore L := by rw [hcore]; exact ⟨hzS,hzE⟩
  have hQS : twoCore L ≤ (S : Subgroup H).map H.subtype := by
    rw [hcore]; exact inf_le_left
  have hQN : twoCore L ≤ normalizer (R : Set G) := by rwa [hcore]
  have hCQ : (S : Subgroup H).map H.subtype ⊓ centralizer (R : Set G) ≤ twoCore L := by
    rw [hcore]; exact le_inf inf_le_left hCR
  exact crossing_normal_two_false c hG hp hUS (Q := twoCore L) (R := R)
    (pCore_isPGroup.map L.subtype) hzQ (le_normalizer_twoCore L)
    hQS hQN hCQ hxT hxS hxN hxR
end CFSG.Quasithin.Chapter2.Section05
