module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Module.MovingThompson
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.CatalogueExclusions

/-!
# The escaping Hall component after local Thompson movement

For the intrinsic Hall subgroup of the original H-star member, local
Thompson movement now discharges full-module fixation. A nontrivial kernel
therefore has an actual escaping normal component with trivial two-core.
The earlier shared-sporadic, binary rank-one, Suzuki and Tits exclusions
apply to this same component, with its full center and Hall maps retained.

The remaining component rows still require exclusion. This is an actual
application of module fixation, not unconditional Hall faithfulness.
Source: Aschbacher--Smith 10.2.3(2), printed p.745, using 4.4.3.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original moving-Thompson Hall kernel has only the already specified
remaining zero-two-core component rows, with module fixation discharged. -/
theorem source_hstar_hall_kernel_escaping_component_of_local_thompson
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hJ : ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {n : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP n)
    (hk : d.witness.abelianGroup ⊓
      (sectionCentralizer (localOrbit T L)).subgroupOf H ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧
      Nat.Coprime p (Nat.card (L ⧸ pCore 2 L)) ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ d.witness.abelianGroup.map H.subtype ∧
      A ≤ sectionCentralizer (localOrbit T L) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ D.maximalLocal ∧
      pCore 2 (normalizer (A : Set G)) = ⊥ ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
        ⁅K,D.fullModule.subgroupOf (normalizer (A : Set G))⁆ = K ∧
        ¬ K.map (normalizer (A : Set G)).subtype ≤ D.maximalLocal ∧
        pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
        ¬ (ChapterA.Section02.IsTheoremCSporadicModel (K ⧸ center K) ∨
          (∃ n, 2 ≤ n ∧ ClassicalGroup.IsPSL (K ⧸ center K) 2 (2^n)) ∨
          ∃ m, 1 ≤ m ∧ Nonempty
            (K ⧸ center K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∧
        ¬ Nonempty (K ⧸ center K ≃* Tits.ParrottGroup) := by
  have he := source_hstar_parabolicMax_eq_overlap D hH hP
  exact source_hstar_hall_kernel_escaping_component_catalogue_remainder D hn hH hlarge hP d hk
    (source_hall_kernel_fixes_of_local_thompson D hmin hn hna hJ d.witness.abelianGroup
      (he ▸ d.hall_le) (he ▸ d.hall))

end CFSG.Quasithin.Chapter10
