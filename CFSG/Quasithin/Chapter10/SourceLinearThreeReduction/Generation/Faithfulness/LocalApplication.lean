module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalNormality
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.ReselectionApplication

/-!
# The actual Hall-kernel component without full-module fixation

A nontrivial intrinsic Hall kernel forces the quiet branch. It fixes the
nonzero Sylow-fixed orbit, which is fully moved by L₀. The local-module
normalizer argument therefore gives covering uniqueness, trivial two-core,
and an ordinary component outside M moved by this very orbit. The odd core
centralizes the orbit and lies in M. The component retains its full center
and Theorem B catalogue; its action and every subgroup map remain literal.

This proves covering uniqueness, two-core vanishing, odd-core control and
normal-component detection for the surviving literal Hall kernel without
assuming fixation of V_M. Residual placement and the remaining component
exclusions for this local module are still needed for full Hall faithfulness.
Source: Aschbacher--Smith 4.4.5--10 and10.2.3(2), printed pp.620--621,745
(combined manuscript of 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The remaining original Hall counterexample has a zero-two-core normalizer
with a component moved by the actual Sylow-fixed orbit; no fixation callback remains. -/
theorem source_hall_kernel_escaping_local_component
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
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
      A ≤ centralizer (sourceQuietFixedSpan D : Set G) ∧
      8 < Nat.card (sourceQuietFixedSpan D) ∧
      UniqueMaximalOvergroup
        ((solvableResidual (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
          (localOrbit T L ⊓ centralizer (A : Set G)).subtype ⊔
          ((T : Subgroup G) ⊓ normalizer (A : Set G))) D.maximalLocal ∧
      ⁅sourceQuietFixedSpan D,(pPrimeCore 2 (normalizer (A : Set G))).map
        (normalizer (A : Set G)).subtype⁆ = ⊥ ∧
      (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype ≤ D.maximalLocal ∧
      pCore 2 (normalizer (A : Set G)) = ⊥ ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
        ⁅K,(sourceQuietFixedSpan D).subgroupOf (normalizer (A : Set G))⁆ = K ∧
        ¬ K.map (normalizer (A : Set G)).subtype ≤ D.maximalLocal ∧
        pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) ∧
        ((solvableResidual (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
          (localOrbit T L ⊓ centralizer (A : Set G)).subtype).subgroupOf
            (normalizer (A : Set G)) ≤ normalizer (K : Set (normalizer (A : Set G))) ∧
        (sourceQuietFixedSpan D).subgroupOf (normalizer (A : Set G)) ≤
          normalizer (K : Set (normalizer (A : Set G))) := by
  have he := source_hstar_parabolicMax_eq_overlap D hH hP
  have hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G) := by
    by_contra hmove
    exact hk (source_hstar_hall_kernel_eq_bot_of_full_fixation D hn hH hlarge hP d
      (source_hall_kernel_fixes_of_local_thompson D hmin hn hna hmove
        d.witness.abelianGroup (he ▸ d.hall_le) (he ▸ d.hall)))
  have hfix : d.witness.abelianGroup.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤
      centralizer (sourceQuietFixedSpan D : Set G) :=
    source_hall_kernel_fixes_fixed_span_of_local_thompson_centralizes D hJ hH
      d.witness.abelianGroup (he ▸ d.hall_le) (he ▸ d.hall)
  obtain ⟨p,A,hp,ho,hcop,hne,hAe,hAY,hAC,hAT,hout⟩ :=
    source_hstar_hall_kernel_escaping_coprime D hn hH hlarge hP d hk
  let : Fact p.Prime := ⟨hp⟩
  let := hAe
  have hAp := IsElementaryAbelian.isPGroup p A
  have hAW := (le_inf hAY hAC).trans hfix
  have hWV := sourceQuietFixedSpan_le D
  have hWne := sourceQuietFixedSpan_ne_bot D
  have hWX := (sourceQuietFixedSpan_commutator D hmany hJ).symm
  have hNW := sourceQuietFixedSpan_normalized D
  have hu := source_local_oddPrimeActor_covering_uniqueness D hn _ hWV hWne hWX hNW
    ho A hAp hAC hAW hAT
  have hsize := source_local_oddPrimeActor_module_card_gt_eight D hn _ hWV hWne hWX hNW
    ho A hAp hAC hAW hAT
  obtain ⟨hcomm,hOM⟩ := source_local_oddPrimeActor_oddCore D hn _ hWV hWne hWX hNW
    ho A hAp hAC hAW hAT
  have hcomponent := source_local_oddPrimeActor_moved_component D hn _ hWV hWne hWX hNW
    ho A hne hAp hAC hAW hAT hout
  obtain ⟨hcore,K,hK,hmove,houtK,hKcore,hmodel,hFK,hWK⟩ := hcomponent
  have hodd : Odd (Nat.card A) := by
    obtain ⟨k,he⟩ := hAp.exists_card_eq
    rw [he]
    exact ho.pow
  have hnormal := source_local_oddActor_component_normal D _ hWV hWne hWX hNW
    A hne hAC hodd hAW hcore K hK houtK hFK
  exact ⟨p,A,hp,ho,hcop,hne,hAe,hAY,hAC,hAT,hout,hAW,hsize,hu,hcomm,hOM,
    hcore,K,hK,hnormal,hmove,houtK,hKcore,hmodel,hFK,hWK⟩

end CFSG.Quasithin.Chapter10
