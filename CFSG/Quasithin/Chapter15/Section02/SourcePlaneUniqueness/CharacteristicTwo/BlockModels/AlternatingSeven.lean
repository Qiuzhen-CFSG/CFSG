module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.Orbits
public import CFSG.Quasithin.ChapterC.Section01.RankOne.LocalC129.ChiSieve
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.PrimeComplement
public import Theory.SpecificGroups.Alternating.SevenComponent

/-!
# Residual containment for the ordinary A7 block

The actual normal A7 block has three-prime index: its centerless quotient
contains an elementary nine and its outer group is a two-group. Its intrinsic
prime-to-three residual is the whole block, so the ambient O^{3′}(I) equals
that block. The original wreath quotient makes H a {2,3}-group; consequently
its O² image belongs to this same residual inside I.

The final consumer places the original K inside C_X(ZS), with the actual
ambient maps. The partition marking and action exclusion remain separate
obligations of qt-e-152-char2-block-exclusion.
Source: Aschbacher--Smith, A.3.18 and preliminary 15.2.23, printed pp.51--52
and 1115, refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
open Section01 Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d hsource

omit d in
/-- The actual A7 block has index prime to three in I. -/
theorem a7_block_index_coprime_three (hI : PlaneEscapes Mc ZS I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X)
    (hb : ChapterC.IsAlternatingBlock X 7) : Nat.Coprime 3 X.index := by
  have hs := (Chapter3.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin
  let : X.Normal := ChapterC.LocalC129.alternating_seven_normal hs hX hb
  obtain ⟨e⟩ := hb.2.2.quotient_iso
  let : IsQuasisimple (alternatingGroup (Fin 7)) :=
    { toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
      simple := by
        let : IsSimpleGroup (alternatingGroup (Fin 7)) :=
          alternatingGroup.isSimpleGroup (by simp)
        exact ((QuotientGroup.quotientMulEquivOfEq
          (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (X ⧸ pCore 2 X) := IsQuasisimple.of_mulEquiv e.symm
  have hC : X.IsCComponent :=
    isCComponent_of_isPPerfect_of_quasisimple_core_quotient hX.subnormal hb.2.1.twoPerfect
  have hz : center (X ⧸ pCore 2 X) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have he := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center (alternatingGroup (Fin 7)) at he
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at he
    exact e.map_eq_one_iff.mp he
  have hr : 2 ≤ primeRank 3 (X ⧸ pCore 2 X) := by
    rw [primeRank_congr 3 e]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  have ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (X ⧸ pCore 2 X))) := by
    rw [Nat.card_congr (MulAut.outerCongr e).toEquiv]
    obtain ⟨n,hn⟩ := alternatingGroup.SevenComponent.outer_two.exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 3 2).pow_right n).coprime_dvd_right hn
  exact cComponent_index_coprime_three_of_quotient X hC hz hr
    (hs 3 (by decide) (by decide)) ho

omit d in
/-- The block equals the literal ambient prime-to-three residual. -/
theorem a7_block_eq_threeResidual (hI : PlaneEscapes Mc ZS I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X)
    (hb : ChapterC.IsAlternatingBlock X 7) : primeToResidual 3 I = X := by
  obtain ⟨e⟩ := hb.2.2.quotient_iso
  let : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (X ⧸ pCore 2 X) := e.isSimpleGroup
  have hd : 3 ∣ Nat.card (X ⧸ pCore 2 X) := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hr := primeToResidual_eq_top_of_simple_quotient 3 2 (pCore 2 X)
    pCore_isPGroup hb.2.1.twoPerfect hd
  exact primeToResidual_eq_of_subnormal_coprime_index 3 X hX.subnormal hr
    (a7_block_index_coprime_three (hsource := hsource) hI hX hb)

/-- The source two-residual, with its original embedding, belongs to the block. -/
theorem a7_block_contains_residual (hI : PlaneEscapes Mc ZS I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X)
    (hb : ChapterC.IsAlternatingBlock X 7) :
    (pResidual 2 H).map H.subtype ≤ X.map I.subtype := by
  obtain ⟨eH⟩ := d.geometry.quotient
  have hpi := ChosenGeometry.twoThree_of_wreath H eH
  let K := (pResidual 2 H).map H.subtype
  have hKI : K ≤ I := le_sup_left.trans
    ((d.residual_sup_planeSylow_le hI).trans inf_le_right)
  let K' := K.subgroupOf I
  let e : (pResidual 2 H) ≃* K' :=
    ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (subgroupOfEquivOfLe hKI).symm
  have hp : IsPPerfect 2 K' := (isPPerfect_pResidual 2 (G := H)).of_surjective
    e.toMonoidHom e.surjective
  have hKpi : IsPiGroup twoThreePrimes K' :=
    (hpi.of_injective (pResidual 2 H).subtype (pResidual 2 H).subtype_injective).of_equiv e.symm
  have hr : primeToResidual 3 K' = ⊤ := by
    rw [← twoResidual_eq_primeToResidual_three hKpi]
    exact (pResidual_eq_top_iff 2 K').mpr hp
  have hKX : K' ≤ X := by
    rw [← a7_block_eq_threeResidual (hsource := hsource) hI hX hb]
    exact le_primeToResidual_of_eq_top 3 K' hr
  have hh := map_mono (f := I.subtype) hKX
  rwa [map_subgroupOf_eq_of_le hKI] at hh

/-- The residual containment supplies the source premise K ≤ M₀. -/
theorem a7_block_residual_le_centralizer (hI : PlaneEscapes Mc ZS I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X)
    (hb : ChapterC.IsAlternatingBlock X 7) :
    (pResidual 2 H).map H.subtype ≤
      X.map I.subtype ⊓ centralizer (ZS : Set G) :=
  le_inf (d.a7_block_contains_residual hI hX hb) d.residual_centralizes

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding
