module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.OriginalLocalClass
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.HStarCoverage
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.HStarOddFixedCenter
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.CharacteristicSource

/-!
# The general-field moving pair has an original block

The original and comparison local groups use the literal ambient Baumann
inclusions. Their common characteristic pair forces a block in the original
component or in the same selected comparison component. Its generation and
natural quotient markings are retained for the subsequent Cartan-axis step.

Both fixed centers are eliminated using the original odd Hall action.
The moving-Hall assembly owner still owes the earlier Hall containment
and seed-centralizer identity.
Source: Aschbacher–Smith C.1.18–19 and 10.2.3(4), printed pp.746–747.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open ChapterB Chapter3.Section02 ChapterC.GlaubermanNiles ChapterC.RankOne.ChiProduct
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem component_twoPerfect {A : Type*} [Group A] [Finite A]
    {K : Subgroup A} (hK : K.IsCComponent) : IsPPerfect 2 K := by
  let := hK.perfect
  intro Q hQ hp
  let := hQ
  let : Group.IsNilpotent (K ⧸ Q) := hp.isNilpotent
  apply top_unique
  rw [←solvableResidual_eq_top (G := K)]
  exact solvableResidual_le_of_solvable_quotient Q

set_option backward.isDefEq.respectTransparency false in
theorem Context.one_block_of_intrinsic_localClass
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G)=⊥)
    (hzH : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G)=⊥)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hBK : baumann (T.subtype ctx.hstar.1.1.2 : Subgroup H) ≤ normalizer (K : Set H))
    (hlocal : InLocalClass (inclusion (show baumann (T.subtype ctx.hstar.1.1.2 : Subgroup H) ≤
      K ⊔ baumann (T.subtype ctx.hstar.1.1.2 : Subgroup H) from le_sup_right)))
    (hgen : K ⊔ (T.subtype ctx.hstar.1.1.2 : Subgroup H)=⊤) :
    ChapterC.IsBlock (L.subgroupOf (localJoin T L)) ∨
      (ChapterC.IsBlock K ∧ ∃ m, ChapterC.IsL2EvenBlock K m) := by
  let X := localJoin T L
  let SX := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let A := L.subgroupOf X
  let BX := baumann (SX : Subgroup X)
  let BH := baumann (T.subtype ctx.hstar.1.1.2 : Subgroup H)
  let NL := A ⊔ BX
  let NH := K ⊔ BH
  let iL := X.subtype.comp NL.subtype
  let iH := H.subtype.comp NH.subtype
  have hLX : L ≤ X := (le_componentOrbit L T).trans le_sup_left
  have hA : A.IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  have hsource := ctx.original_common_baumann_embedding D n hn hF e
  obtain ⟨bL,hbL,hiL⟩ := hsource.2.2.2.2
  obtain ⟨bH,hbH,hiH⟩ := original_baumann_embedding (T : Subgroup G) H ctx.hstar.1.1.2
    NH (show BH ≤ NH from le_sup_right) hlocal
  have hLrange : L ≤ iL.range := by
    intro l hl
    exact ⟨⟨⟨l,hLX hl⟩,(le_sup_left : A ≤ NL) hl⟩,rfl⟩
  have hLgen : localOrbit T L ≤ iL.range ⊔ (T : Subgroup G) := by
    have hh : localOrbit T L ≤ L ⊔ (T : Subgroup G) := by
      rw [←componentOrbit_sup]
      exact le_sup_left
    exact hh.trans (sup_le_sup_right hLrange _)
  have hKrange : K.map H.subtype ≤ iH.range := by
    rintro k ⟨a,ha,rfl⟩
    exact ⟨⟨a,(le_sup_left : K ≤ NH) ha⟩,rfl⟩
  have hHgen : H ≤ iH.range ⊔ (T : Subgroup G) := by
    have hTm : (T.subtype ctx.hstar.1.1.2 : Subgroup H).map H.subtype=(T : Subgroup G) :=
      map_subgroupOf_eq_of_le ctx.hstar.1.1.2
    have hh := congrArg (map H.subtype) hgen
    rw [Subgroup.map_sup,hTm,
      ←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh.symm.le.trans (sup_le_sup_right hKrange _)
  rcases source_hstar_selected_block_alternative_of_embeddings D ctx.hstar hz hzH
      NL NH iL iH bL bH hiL hiH hLgen hHgen hbL hbH with hb | hb
  · exact Or.inl (SelectedRankOne.selected_component_chi_of_blockAlternative
      SX A hA (component_twoPerfect hA) hsource.2.1 hb).1
  · exact Or.inr (SelectedRankOne.selected_component_natural_of_blockAlternative
      (T.subtype ctx.hstar.1.1.2) K hK (component_twoPerfect hK) hBK hb)

/-- Applying the common characteristic pair to the same component produced
by H-star classification. The odd-order fixed-center theorems discharge
both fixed-center premises; no new comparison component is selected. -/
theorem Context.selected_component_and_block
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hBR : B.map H.subtype ≤ localOrbit T L)
    (hCZ : centralizer ((omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) =
      (T.subtype ctx.hstar.1.1.2 : Subgroup H)) :
    let S := T.subtype ctx.hstar.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    let B₀ := baumann (S : Subgroup H)
    ∃ K : Subgroup H, K.IsCComponent ∧
      U ≤ normalizer (K : Set H) ∧ B₀ ≤ normalizer (K : Set H) ∧
      InLocalClass (inclusion (show B₀ ≤ K ⊔ B₀ from le_sup_right)) ∧
      (localV (inclusion (show B₀ ≤ K ⊔ B₀ from le_sup_right))).map
        (K ⊔ B₀).subtype = (⁅U,K⁆ : Subgroup H) ⊔
          (thompsonAlpha (S : Subgroup H) ⊓ centralizer (K : Set H)) ∧
      K ⊔ (S : Subgroup H) = ⊤ ∧
      (K = pResidual 2 H ∨
        ((thompsonAlpha (S : Subgroup H) ⊓ centralizer (K : Set H) ≠ ⊥) ∧
          (∃ E : ChapterB.QuasisimpleSource.BinaryField,
            Nonempty ((K ⧸ pCore 2 K) ≃* SL(2,E.Carrier))) ∧
          ∃ t ∈ (S : Subgroup H),
            pResidual 2 H = K ⊔ K.map (MulAut.conj t).toMonoidHom)) ∧
      (ChapterC.IsBlock (L.subgroupOf (localJoin T L)) ∨
        (ChapterC.IsBlock K ∧ ∃ m, ChapterC.IsL2EvenBlock K m)) := by
  obtain ⟨K,hK,hUK,hBK,hlocal,hv,hgen,hkind⟩ :=
    ctx.hstar_component_coverage_of_seed_centralizer D n hn hF e hCZ
  obtain ⟨hz,hzH⟩ := ctx.original_fixed_centers_eq_bot D n hn hF e hBR hCZ
  exact ⟨K,hK,hUK,hBK,hlocal,hv,hgen,hkind,
    ctx.one_block_of_intrinsic_localClass D n hn hF e hz hzH K hK hBK hlocal hgen⟩

end CFSG.Quasithin.Chapter10.MovingHall
