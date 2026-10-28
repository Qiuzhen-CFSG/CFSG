module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.SingleComparison
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.RankTwoModels
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction

/-!
# Original Hall placement for every rank-two single comparison

The actual common overcomponent is relatively normal, so the original
Sylow meets it in a Sylow. Solvability of B₀T and the concrete quotient
geometry make B₀ fix the quotient Sylow and then each of its two local
components. The two-core normalizes the original perfect comparison,
so the quotient invariance lifts to B₀ ≤ N_G(K). The existing residual,
field-factor and coprime-lifting proofs place the original Hall in B₀.

Source: Aschbacher–Smith 10.2.3, printed p.746, case (b). The model sieve
and its other cases remain with this task's final source assembly.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Subgroup Theory.GroupTheory Chapter3.Section02 ChapterA.Section03
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} {ctx : Context D H B}

/-- Solvable Sylow control and a local pair in the literal two-core quotient
give Borel normalization of the original single comparison. -/
theorem ComparisonConfiguration.borel_normalizes_of_single_geometry
    (c : ComparisonConfiguration D ctx) (hsingle : c.component = pResidual 2 H)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hcontrol : SolvableSylowControl 2 (c.overcomponent ⧸ pCore 2 c.overcomponent))
    (hpair : ∀ S : Sylow 2 (c.overcomponent ⧸ pCore 2 c.overcomponent),
      ∃ P Q : Subgroup (c.overcomponent ⧸ pCore 2 c.overcomponent),
        ∀ K : Subgroup (c.overcomponent ⧸ pCore 2 c.overcomponent),
          K ∈ localCComponents S → K ≠ ⊤ → K = P ∨ K = Q) :
    sourceOrbitBorel T L ≤ normalizer (c.component.map H.subtype : Set G) := by
  let I := c.overcomponent
  let K := c.component.map H.subtype
  let A := sourceOrbitBorel T L
  let P := A ⊔ (T : Subgroup G)
  have hKI : K ≤ I := c.component_le
  have hPI : P ≤ normalizer (I : Set G) :=
    sup_le c.borel_normalizes (c.single_overcomponent_normalized D hsingle)
  let := c.component_isCComponent.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (c.component.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom)
    (c.component.equivMapOfInjective H.subtype H.subtype_injective).surjective
  let : Group.IsSolvable P := original_borel_sylow_solvable D ctx e
  obtain ⟨S,hS⟩ := c.single_sylow D hsingle
  have hSP : (S : Subgroup I).map I.subtype ≤ P := by
    rw [hS,subgroupOf_map_subtype]
    exact inf_le_left.trans le_sup_right
  have hs := core_quotient_sylow_invariant I A P le_sup_left hPI S hSP hcontrol
  let q := QuotientGroup.mk' (pCore 2 I)
  let Sb := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 I))
  let a := (normalizerQuotientAction I (pCore 2 I)).comp (inclusion (le_sup_left.trans hPI))
  have hp : IsPPerfect 2 A := isPPerfect_embedded_pResidual 2 (sourceOrbitSylowNormalizer T L)
  have hl : K.subgroupOf I ∈ localCComponents S := by
    rw [hS]
    exact SourceEmbeddings.local_restrict (c.local_components D).1.1 hKI
  let : Group.IsSolvable q.ker := by
    rw [show q.ker = pCore 2 I from QuotientGroup.ker_mk' _]
    let := pCore_isPGroup (p := 2) (G := I) |>.isNilpotent
    infer_instance
  have hlb : (K.subgroupOf I).map q ∈ localCComponents Sb :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hl q
  apply normalizes_perfect_of_core_quotient_invariant I K A hKI
    (le_sup_left.trans hPI) (c.single_core_normalizes D hsingle)
  exact twoPerfect_fixes_local_pair a hp Sb hs (hpair Sb) _ hlb

/-- Each of the three rank-two quotients gives Borel normalization of the original single
comparison, with the original two-core and original Sylow retained. -/
theorem ComparisonConfiguration.borel_normalizes_of_single_rank_two
    (c : ComparisonConfiguration D ctx) (hsingle : c.component = pResidual 2 H)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hmodel : ComparisonRankTwo (c.overcomponent ⧸ pCore 2 c.overcomponent)) :
    sourceOrbitBorel T L ≤ normalizer (c.component.map H.subtype : Set G) := by
  obtain ⟨hcontrol,hpair⟩ := comparison_rank_two_geometry hmodel
  exact c.borel_normalizes_of_single_geometry D hsingle e hcontrol hpair

/-- Actual Hall placement in the single rank-two comparison branch. -/
theorem ComparisonConfiguration.hall_le_borel_of_single_rank_two
    (c : ComparisonConfiguration D ctx) (hsingle : c.component = pResidual 2 H)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hmodel : ComparisonRankTwo (c.overcomponent ⧸ pCore 2 c.overcomponent)) :
    B.map H.subtype ≤ sourceOrbitBorel T L :=
  c.hall_le_borel_of_normalizes D e
    (c.borel_normalizes_of_single_rank_two D hsingle e hmodel)
end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
