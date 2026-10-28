module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelLift
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.ProductCoordinates

/-!
# Borel transport in the moving linear-two component orbit

The product-coordinate leaf constructs the actual product in H/O₂(H),
marking both component inclusions and the moving conjugation. Here
normalization of a chosen star subgroup is transported to its lift inside
K₀. Together with 13.8.13 this puts the normalized solvable lift in M.

This transport leaf is used by SourceBorel to construct the Borel from
the Sylow intersection and the actual product coordinates.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.8.16(1), printed p.952; Notation 13.2.1, printed p.877.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo
variable {G : Type*} [Group G]

/-- Elementwise specification of the lift, retaining membership in the orbit. -/
theorem mem_borelLift_iff (H K₀ : Subgroup G) (hK : K₀ ≤ H)
    (Bstar : Subgroup (Source.Hstar H)) (x : G) :
    x ∈ borelLift H K₀ hK Bstar ↔
      ∃ hx : x ∈ K₀, QuotientGroup.mk' (pCore 2 H) ⟨x, hK hx⟩ ∈ Bstar := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · rintro ⟨hx, hb⟩
    exact ⟨⟨x, hx⟩, hb, rfl⟩

/-- Normalization of the actual image and of K₀ gives normalization of its
lift. The normality hypotheses are local, not ambient normality of K₀. -/
theorem borelLift_normalized (H K₀ A : Subgroup G) (hK : K₀ ≤ H) (hA : A ≤ H)
    (Bstar : Subgroup (Source.Hstar H)) (hnK : A ≤ normalizer (K₀ : Set G))
    (hnB : Source.starImage H A ≤ normalizer (Bstar : Set (Source.Hstar H))) :
    A ≤ normalizer (borelLift H K₀ hK Bstar : Set G) := by
  apply le_normalizer_iff.mpr
  intro a ha x hx
  obtain ⟨hxK, hxB⟩ := (mem_borelLift_iff H K₀ hK Bstar x).mp hx
  have hyK : a * x * a⁻¹ ∈ K₀ := (mem_normalizer_iff.mp (hnK ha) x).mp hxK
  apply (mem_borelLift_iff H K₀ hK Bstar _).mpr
  refine ⟨hyK, ?_⟩
  let q := QuotientGroup.mk' (pCore 2 H)
  have haS : q (⟨a, hA ha⟩ : H) ∈ Source.starImage H A :=
    mem_map_of_mem q (show (⟨a, hA ha⟩ : H) ∈ A.subgroupOf H from ha)
  have hh := (mem_normalizer_iff.mp (hnB haS) (q ⟨x, hK hxK⟩)).mp hxB
  have he : (⟨a * x * a⁻¹, hK hyK⟩ : H) =
      (⟨a, hA ha⟩ : H) * ⟨x, hK hxK⟩ * (⟨a, hA ha⟩ : H)⁻¹ := rfl
  change q ⟨a * x * a⁻¹, hK hyK⟩ ∈ Bstar
  rwa [he, map_mul, map_mul, map_inv]

/-- The earlier universal solvable exclusion applies after normalization
has been checked on the actual star image. -/
theorem borelLift_le_M_of_star_normalized [Finite G]
    (H K₀ L₁ T G₁ M : Subgroup G) (hK : K₀ ≤ H) (hA : L₁ ⊔ T ≤ H)
    (Bstar : Subgroup (Source.Hstar H))
    [Group.IsSolvable Bstar] [Group.IsSolvable (L₁ ⊔ T : Subgroup G)]
    (hnK : L₁ ⊔ T ≤ normalizer (K₀ : Set G))
    (hnB : Source.starImage H (L₁ ⊔ T) ≤ normalizer (Bstar : Set (Source.Hstar H)))
    (hKG : K₀ ≤ G₁) (hbase : L₁ ⊔ T ≤ G₁)
    (hex : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M) : borelLift H K₀ hK Bstar ≤ M :=
  borelLift_le_M H K₀ L₁ T G₁ M hK Bstar
    (borelLift_normalized H K₀ (L₁ ⊔ T) hK hA Bstar hnK hnB) hKG hbase hex

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo

end
