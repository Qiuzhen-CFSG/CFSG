module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.SmallRank
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.Tits
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.CoveringClosure

/-!
# Applying the small-rank exclusions to the original Hall kernel

Covering uniqueness gives residual placement for the normal component
produced by an escaping kernel. Its full module action then excludes J₂,
HS, Rudvalis and the Tits group. The final theorem retains the original Hall subgroup,
two-core quotient, normal component and moved-module data, and removes
these four rows from the existing zero-two-core reduction.

Source: Aschbacher--Smith 4.4.3 and 10.2.3(2), pp.619--623,745.
Fixation and the remaining component rows are still required for the
unconditional source theorem.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The three small-rank sporadic rows are impossible for the literal Hall
kernel, with covering uniqueness and residual placement discharged. -/
theorem source_hall_kernel_no_small_rank_sporadic_component
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
    (hm : Nonempty (K ⧸ center K ≃* Sporadic.LeechRelated.J2.Carrier) ∨
      Nonempty (K ⧸ center K ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty (K ⧸ center K ≃* Rudvalis.Model)) : False := by
  let := hA
  have ho : Odd (Nat.card A) := by
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact hp.pow
  have hAV := (le_inf hAY hAC).trans hfix
  have hu := source_nonnormal_oddPrimeActor_covering_uniqueness D hn hp A
    (IsElementaryAbelian.isPGroup p A) hAC hAV hAT
  rcases hm with ⟨e⟩ | ⟨e⟩ | ⟨e⟩
  · exact source_nonnormal_oddNormalizer_no_jankoTwo_component D hn A hAC ho hAV hu K hK hout hc e.some
  · exact source_nonnormal_oddNormalizer_no_higmanSims_component D hn A hAC ho hAV hu K hK hout hc e.some
  · exact source_nonnormal_oddNormalizer_no_rudvalis_component D hn A hAC ho hAV hu K hK hout hc e.some

/-- The literal elementary Hall kernel cannot have a Tits normalizer
component; uniqueness and residual placement are both discharged. -/
theorem source_hall_kernel_no_tits_component
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
    (e : K ⧸ center K ≃* Tits.ParrottGroup) : False := by
  let := hA
  have ho : Odd (Nat.card A) := by
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact hp.pow
  have hAV := (le_inf hAY hAC).trans hfix
  have hu := source_nonnormal_oddPrimeActor_covering_uniqueness D hn hp A
    (IsElementaryAbelian.isPGroup p A) hAC hAV hAT
  exact source_nonnormal_oddNormalizer_no_tits_component D hn A hAC ho hAV hu K hK hout e

/-- The escaping original Hall kernel supplies a normal component outside
the three small-rank sporadic rows and the Tits row. Fixation remains explicit. -/
theorem source_hstar_hall_kernel_escaping_component_finite_exclusions
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
        ¬ (Nonempty (K ⧸ center K ≃* Sporadic.LeechRelated.J2.Carrier) ∨
          Nonempty (K ⧸ center K ≃* Sporadic.LeechRelated.HS.Carrier) ∨
          Nonempty (K ⧸ center K ≃* Rudvalis.Model)) ∧
        ¬ Nonempty (K ⧸ center K ≃* Tits.ParrottGroup) := by
  obtain ⟨p,A,hp,ho,hcop,hA,hAe,hAY,hAC,hAT,hout,hc,K,hK,hKn,hm,houtK,hcK,hmodel⟩ :=
    source_hstar_hall_kernel_escaping_normal_component D hn hH hlarge hP d hk hfix
  let : Fact p.Prime := ⟨hp⟩
  let := hKn
  exact ⟨p,A,hp,ho,hcop,hA,hAe,hAY,hAC,hAT,hout,hc,K,hK,hKn,hm,houtK,hcK,hmodel,
    source_hall_kernel_no_small_rank_sporadic_component D hn d.witness.abelianGroup
      hfix ho A hAe hAY hAC hAT K hK houtK hcK,
    fun ⟨e⟩ => source_hall_kernel_no_tits_component D hn d.witness.abelianGroup
      hfix ho A hAe hAY hAC hAT K hK houtK e⟩

end CFSG.Quasithin.Chapter10
