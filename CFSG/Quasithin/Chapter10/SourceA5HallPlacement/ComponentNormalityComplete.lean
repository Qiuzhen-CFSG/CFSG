module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.ComponentNormality
public import CFSG.Quasithin.ChapterA.Section03.QTComponents.RemainingRows

/-!
# Normality of the original Hall normalizer component

The complete model-local rank families discharge the final input of the
five-row nonnormal-component inspection. Its original perfect-core exclusions
therefore force normality of the actual selected escaping component. No
catalogue, rank or outer-action callback remains in this normality theorem.
Placement and inspection of the resulting normal component are separate.

Source: Aschbacher–Smith4.4.9–11, p.621, using A.3.8(1–2), pp.45–46.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual escaping component is normal, with all model-local families
proved and applied to its literal central quotient. -/
theorem source_a5_oddNormalizer_component_normal
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G)))) : K.Normal := by
  exact source_a5_oddNormalizer_component_normal_of_remaining_local
    D e hn hp B hne hB hBC hBV hperm K hK houtK hFK
    ChapterA.QTComponents.remainingLocalInput

end CFSG.Quasithin.Chapter10
