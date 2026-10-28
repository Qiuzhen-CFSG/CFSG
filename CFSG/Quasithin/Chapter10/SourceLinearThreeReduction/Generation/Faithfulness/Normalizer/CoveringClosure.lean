module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.OrdinaryHeld
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.HeldSource
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.Reduction

/-!
# Covering uniqueness and the nontrivial-two-core Hall normalizer case

The last ordinary covering row is excluded by the full Held component
calculation. The original inclusion-compatible intersection quotient carries
the centerless seed hypothesis, so the genuine C.2.8 counterexample is now
impossible. This gives covering uniqueness for the fixed residual joined
with the original Sylow normalizer.

Applied to an elementary subgroup of the literal Hall image intersected
with the section centralizer, uniqueness puts its normalizer in M whenever
the normalizer has nontrivial two-core. Hence an escaping Hall kernel that
fixes the full module has only the normal-component branch with trivial
two-core. Module fixation and that remaining component inspection are still
required for unconditional Hall faithfulness.

Source: Aschbacher--Smith 4.4.6--7 and 4.4.10--12, pp.620--623,
used in 10.2.3(2), p.745.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Uniqueness for the original covering subgroup, with the entire C.2.8 remainder excluded. -/
theorem source_nonnormal_covering_uniqueness
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {I : Subgroup G} (hIM : I ≤ D.maximalLocal)
    (hcover : (localOrbit T L : Set G) ⊆
      (I : Set G) * ((localOrbit T L).pCoreIn 2 : Set G))
    (hcore : I.pCoreIn 2 ≠ ⊥)
    (horbit : componentOrbit L I = localOrbit T L) :
    UniqueMaximalOvergroup I D.maximalLocal := by
  by_contra hnot
  obtain ⟨J,H,S,_,_,_,_,hC,hnorm,⟨e,_⟩,K,hK,_,hzK,⟨a⟩⟩ :=
    source_nonnormal_covering_held_remainder D hn hIM hcover hcore horbit hnot
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let := D.quasisimple
  let : IsQuasisimple (LH ⧸ pCore 2 LH) := IsQuasisimple.of_mulEquiv e.symm
  have hz : center (LH ⧸ pCore 2 LH) = ⊥ := by
    apply bot_unique
    intro x hx
    have hx' := (centerCongr e ⟨x,hx⟩).property
    have he : e x = 1 := (source_nonnormal_component_core_center D hn).le hx'
    exact e.map_eq_one_iff.mp he
  exact hnorm (hC.normalizes_of_simple_ordinary_held hz K hK
    (((QuotientGroup.quotientMulEquivOfEq hzK).trans QuotientGroup.quotientBot).trans a))

/-- The fixed residual joined with the original Sylow normalizer has unique maximal overgroup. -/
theorem source_nonnormal_oddPrimeActor_covering_uniqueness
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup G) (hA : IsPGroup p A)
    (hAC : A ≤ sectionCentralizer (localOrbit T L))
    (hAV : A ≤ centralizer (D.fullModule : Set G))
    (hAT : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G)) :
    UniqueMaximalOvergroup
      ((solvableResidual (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (A : Set G)).subtype ⊔
        ((T : Subgroup G) ⊓ normalizer (A : Set G))) D.maximalLocal := by
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,he⟩ := hA.exists_card_eq
    rw [he]
    exact hp.pow
  let F := (solvableResidual (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
    (localOrbit T L ⊓ centralizer (A : Set G)).subtype
  let I := F ⊔ ((T : Subgroup G) ⊓ normalizer (A : Set G))
  obtain ⟨hIM,_,hcover,hIcore⟩ := source_oddActor_normalizerJoin_input D A hAC hodd hAV
  have hIo : componentOrbit L I = localOrbit T L := by
    apply le_antisymm
    · exact iSup_conjugates_le_of_le_normalizer _ _ _ (le_componentOrbit L T) hIM
    · apply (source_oddPrimeActor_normalizer_orbit D hp A hA hAC hAT).symm.le.trans
      exact iSup_le fun t => le_iSup_of_le
        (⟨t,(show (T : Subgroup G) ⊓ normalizer (A : Set G) ≤ I from le_sup_right)
          t.property⟩ : I) le_rfl
  exact source_nonnormal_covering_uniqueness D hn hIM hcover hIcore hIo

/-- Normalizer containment for the literal Hall kernel when its normalizer two-core is nontrivial. -/
theorem source_hall_kernel_twoCore_normalizer
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (Y : Subgroup H)
    (hfix : Y.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤
      centralizer (D.fullModule : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup G) (hA : IsElementaryAbelian p A)
    (hAY : A ≤ Y.map H.subtype) (hAC : A ≤ sectionCentralizer (localOrbit T L))
    (hAT : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G))
    (hcore : pCore 2 (normalizer (A : Set G)) ≠ ⊥) :
    normalizer (A : Set G) ≤ D.maximalLocal := by
  let := hA
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact hp.pow
  have hAV := (le_inf hAY hAC).trans hfix
  obtain ⟨_,hIN,_,_⟩ := source_oddActor_normalizerJoin_input D A hAC hodd hAV
  have hu := source_nonnormal_oddPrimeActor_covering_uniqueness D hn hp A
    (IsElementaryAbelian.isPGroup p A) hAC hAV hAT
  obtain ⟨N,hN,hAN⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot
    (normalizer (A : Set G)) hcore
  exact (hu.2.2 N hN (hIN.trans hAN)) ▸ hAN

open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan

/-- After module fixation, an escaping original Hall kernel has only the
zero-two-core normal-component branch. Covering uniqueness is discharged. -/
theorem source_hstar_hall_kernel_escaping_normal_component
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
        pCore 2 K = ⊥ ∧ ChapterA.Section02.IsTheoremBModel (K ⧸ center K) := by
  obtain ⟨p,A,hp,ho,hcop,hA,hAe,hAY,hAC,hAT,hout⟩ :=
    source_hstar_hall_kernel_escaping_coprime D hn hH hlarge hP d hk
  let : Fact p.Prime := ⟨hp⟩
  let := hAe
  have hAV : A ≤ centralizer (D.fullModule : Set G) := (le_inf hAY hAC).trans hfix
  have hodd : Odd (Nat.card A) := by
    obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hk]
    exact ho.pow
  have hc : pCore 2 (normalizer (A : Set G)) = ⊥ := by
    by_contra hne
    exact hout (source_hall_kernel_twoCore_normalizer D hn d.witness.abelianGroup
      hfix ho A hAe hAY hAC hAT hne)
  exact ⟨p,A,hp,ho,hcop,hA,hAe,hAY,hAC,hAT,hout,hc,
    source_nonnormal_oddNormalizer_normal_component_of_twoCore D hn A hA hAC hodd hAV hc⟩

end CFSG.Quasithin.Chapter10
