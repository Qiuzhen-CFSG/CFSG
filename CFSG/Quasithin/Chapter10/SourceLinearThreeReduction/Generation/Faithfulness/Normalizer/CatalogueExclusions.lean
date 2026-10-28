module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.HeldNormalizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.RankOneClosure
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.SmallRankApplication

/-!
# Removing shared sporadic and rank-one rows from the escaping component

The Held and J₁ exclusions complete all sporadic rows shared with Theorem C.
Together with the binary SL₂ and Suzuki exclusions, they apply to the actual
normal component selected by an escaping elementary subgroup of the original
Hall kernel. The final reduction retains the component's full center,
normality, trivial two-core and action on the original full module.

Source: Aschbacher--Smith 4.4.3 and 10.2.3(2), printed pp.619--623,745.
The original module-fixation premise and remaining Theorem B component rows
still require proof before unconditional Hall faithfulness can be asserted.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Every sporadic row shared with Theorem C is excluded with its full center. -/
theorem source_nonnormal_oddNormalizer_no_shared_sporadic_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hu : UniqueMaximalOvergroup
      ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype ⊔
        ((T : Subgroup G) ⊓ normalizer (B : Set G))) D.maximalLocal)
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hc : pCore 2 K = ⊥)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel (K ⧸ center K)) : False := by
  rcases hm with ⟨name,hnot,⟨e⟩⟩ | ⟨e⟩
  · cases name with
    | m11 => exact source_nonnormal_oddNormalizer_no_m11_component D hn B hBC hodd hBV hu K hK hout e
    | m12 => exact source_nonnormal_oddNormalizer_no_m12_component D hn B hBC hodd hBV hu K hK hout e
    | m22 => exact source_nonnormal_oddNormalizer_no_m22_component D hn B hBC hodd hBV hu K hK hout e
    | m23 => exact source_nonnormal_oddNormalizer_no_m23_component D hn B hBC hodd hBV hu K hK hout e
    | m24 => exact source_nonnormal_oddNormalizer_no_m24_component D hn B hBC hodd hBV hu K hK hout e
    | j4 => exact source_nonnormal_oddNormalizer_no_jankoFour_component D hn B hBC hodd hBV hu K hK hout hc e
    | j3 => exact hnot rfl
    | j2 => exact source_nonnormal_oddNormalizer_no_jankoTwo_component D hn B hBC hodd hBV hu K hK hout hc e
    | hs => exact source_nonnormal_oddNormalizer_no_higmanSims_component D hn B hBC hodd hBV hu K hK hout hc e
    | he => exact source_nonnormal_oddNormalizer_no_held_component D hn B hBC hodd hBV hu K hK hout hc e
    | ru => exact source_nonnormal_oddNormalizer_no_rudvalis_component D hn B hBC hodd hBV hu K hK hout hc e
  · exact source_nonnormal_oddNormalizer_no_jankoOne_component D hn B hBC hodd hBV K hu hK hout e.some

open scoped Pointwise

/-- Shared sporadic, binary SL₂ and Suzuki rows are impossible for the literal Hall kernel. -/
theorem source_hall_kernel_no_shared_sporadic_or_rank_one_component
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (Y : Subgroup H)
    (hfix : Y.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤
      centralizer (D.fullModule : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup G) (hA : IsElementaryAbelian p A)
    (hAY : A ≤ Y.map H.subtype) (hAC : A ≤ sectionCentralizer (localOrbit T L))
    (hAT : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (A : Set G)).subtype ≤ D.maximalLocal)
    (hc : pCore 2 K = ⊥)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel (K ⧸ center K) ∨
      (∃ n, 2 ≤ n ∧ ClassicalGroup.IsPSL (K ⧸ center K) 2 (2^n)) ∨
      ∃ m, 1 ≤ m ∧ Nonempty (K ⧸ center K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    False := by
  let := hA
  have ho : Odd (Nat.card A) := by
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact hp.pow
  have hAV := (le_inf hAY hAC).trans hfix
  have hu := source_nonnormal_oddPrimeActor_covering_uniqueness D hn hp A
    (IsElementaryAbelian.isPGroup p A) hAC hAV hAT
  rcases hm with hm | ⟨n,hn2,hm⟩ | ⟨m,hm,⟨e⟩⟩
  · exact source_nonnormal_oddNormalizer_no_shared_sporadic_component D hn A hAC ho hAV hu K hK hout hc hm
  · exact source_nonnormal_oddNormalizer_no_binary_sl2_component D hn A hAC ho hAV K hu hK hout hn2 hm
  · exact source_nonnormal_oddNormalizer_no_suzuki_component D hn A hAC ho hAV K hu hK hout hm e
end CFSG.Quasithin.Chapter10

namespace CFSG.Quasithin.Chapter10
open Subgroup Theory.GroupTheory Chapter3.Section02 Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
/-- An escaping fixed-module Hall kernel lies in the remaining Theorem B component rows. -/
theorem source_hstar_hall_kernel_escaping_component_catalogue_remainder
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤)
    {n : ℕ} (d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP n)
    (hk : d.witness.abelianGroup ⊓
      (sectionCentralizer (localOrbit T L)).subgroupOf H ≠ ⊥)
    (hfix : d.witness.abelianGroup.map H.subtype ⊓
      sectionCentralizer (localOrbit T L) ≤ centralizer (D.fullModule : Set G)) :
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
  obtain ⟨p,A,hp,ho,hcop,hA,hAe,hAY,hAC,hAT,hout,hc,K,hK,hKn,hm,houtK,hcK,hmodel⟩ :=
    source_hstar_hall_kernel_escaping_normal_component D hn hH hlarge hP d hk hfix
  let : Fact p.Prime := ⟨hp⟩
  let := hKn
  exact ⟨p,A,hp,ho,hcop,hA,hAe,hAY,hAC,hAT,hout,hc,K,hK,hKn,hm,houtK,hcK,hmodel,
    source_hall_kernel_no_shared_sporadic_or_rank_one_component D hn d.witness.abelianGroup
      hfix ho A hAe hAY hAC hAT K hK houtK hcK,
    fun ⟨e⟩ => source_hall_kernel_no_tits_component D hn d.witness.abelianGroup
      hfix ho A hAe hAY hAC hAT K hK houtK e⟩

end CFSG.Quasithin.Chapter10
