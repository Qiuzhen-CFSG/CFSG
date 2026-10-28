module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.Action
/-!
# Reduction from an original overgroup to KL₁T

Relative component membership and normality descend to KL₁T. Its membership
in Hz is the explicit earlier conclusion 13.8.16(1). The component K and
its intrinsic quotient K/O₂(K) are unchanged. Consequently excluding that
same quotient for the reduced member excludes it for the original H.
No minimality assumption is introduced.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.16(1), 13.8.21–24, printed pp.952, 956–959 (1 March 2004 manuscript).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry
variable {G : Type*} [Group G]

/-- The 13.8.16 reduction retains the original component and its actual
quotient, while descending relative component membership and normality. -/
theorem reduced_component (H K L₁ T : Subgroup G)
    (hKH : K ≤ H) (hbase : L₁ ⊔ T ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hKn : (K.subgroupOf H).Normal) :
    let H₀ := K ⊔ (L₁ ⊔ T)
    H₀ ≤ H ∧ (K.subgroupOf H₀).IsCComponent ∧ (K.subgroupOf H₀).Normal := by
  have h₀ : K ⊔ (L₁ ⊔ T) ≤ H := sup_le hKH hbase
  refine ⟨h₀, hK.subgroupOf_of_le le_sup_left h₀, ?_⟩
  exact (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (h₀.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hKn))

/-- A proof for the reduced source overgroups excludes the original H as
well. The smaller Hz member is exactly the conclusion of 13.8.16(1), not a
minimality assumption. Its K/O₂(K) identification is the original one. -/
theorem exclude_original_of_reduced (L₁ T G₁ M H K : Subgroup G)
    (hH : H ∈ Source.Hz L₁ T G₁ M) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hKn : (K.subgroupOf H).Normal)
    (h16 : K ⊔ (L₁ ⊔ T) ∈ Source.Hz L₁ T G₁ M)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hreduced : ∀ J : Subgroup G, J ∈ Source.Hz L₁ T G₁ M →
      K ≤ J → (K.subgroupOf J).IsCComponent → (K.subgroupOf J).Normal →
      J = K ⊔ (L₁ ⊔ T) →
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) → False) : False := by
  obtain ⟨_, hc, hn⟩ := reduced_component H K L₁ T hKH hH.1.2 hK hKn
  exact hreduced (K ⊔ (L₁ ⊔ T)) h16 le_sup_left hc hn rfl ⟨e⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry
