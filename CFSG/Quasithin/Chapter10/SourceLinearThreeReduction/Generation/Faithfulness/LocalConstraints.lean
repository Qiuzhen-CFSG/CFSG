module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.LocalApplication
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalQuotient

/-!
# Local component exclusions for the literal Hall kernel

The surviving intrinsic Hall kernel fixes the nonzero quiet Sylow-fixed
orbit. Its escaping normal component therefore satisfies the local-module
placement and quotient arguments. The actual component cannot be an
odd-field PSL₂ group or an alternating group of degree at most nine.
The original actor, full covering center, and all residual maps are retained.

The remaining normal-component model branches still belong to the final
Hall-faithfulness assembly; this theorem does not assume or assert full
fixation of V_M.
Source: Aschbacher--Smith 4.4.10--12 and 10.2.3(2), printed pp.621--623,745
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

/-- The actual escaping Hall-kernel component excludes the odd linear-two and small alternating families using the fixed local orbit. -/
theorem source_hall_kernel_escaping_local_component_constraints
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
          normalizer (K : Set (normalizer (A : Set G))) ∧
        (∀ {q : ℕ}, Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ center K) 2 q) ∧
        (∀ {n : ℕ}, n ≤ 9 → ¬ Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin n))) := by
  obtain ⟨p,A,hp,ho,hcop,hne,hAe,hAY,hAC,hAT,hout,hAW,hsize,hu,hcomm,hOM,
    hcore,K,hK,hnormal,hmove,houtK,hKcore,hmodel,hFK,hWK⟩ :=
    source_hall_kernel_escaping_local_component D hmany hmin hn hna hH hlarge hP d hk
  let : Fact p.Prime := ⟨hp⟩
  let := hAe
  let := hnormal
  have hAp := IsElementaryAbelian.isPGroup p A
  have he := source_hstar_parabolicMax_eq_overlap D hH hP
  have hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (D.moduleSubgroup : Set G) := by
    by_contra hmove
    exact hk (source_hstar_hall_kernel_eq_bot_of_full_fixation D hn hH hlarge hP d
      (source_hall_kernel_fixes_of_local_thompson D hmin hn hna hmove
        d.witness.abelianGroup (he ▸ d.hall_le) (he ▸ d.hall)))
  have hWV := sourceQuietFixedSpan_le D
  have hWne := sourceQuietFixedSpan_ne_bot D
  have hWX := (sourceQuietFixedSpan_commutator D hmany hJ).symm
  have hNW := sourceQuietFixedSpan_normalized D
  refine ⟨p,A,hp,ho,hcop,hne,hAe,hAY,hAC,hAT,hout,hAW,hsize,hu,hcomm,hOM,
    hcore,K,hK,hnormal,hmove,houtK,hKcore,hmodel,hFK,hWK,?_,?_⟩
  · intro q hq hm
    exact source_local_oddPrimeActor_no_odd_linear_two_component D hn _ hWV hWne hWX hNW
      A hAC hAW K ho hAp hAT hK houtK hq hm
  · rintro n hdegree ⟨e⟩
    exact source_local_oddPrimeActor_no_alternating_component D hn _ hWV hWne hWX hNW
      A hAC hAW K ho hAp hAT hK houtK hdegree e

end CFSG.Quasithin.Chapter10
