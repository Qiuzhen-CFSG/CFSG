module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.FFSocle
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.OffenderSource
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.Held.Models
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SourceB5.Quasisimple
public import Theory.GroupTheory.CentralizerResidualProducts

/-!
# Full B.5.1 on the actual source star action

The proved C.2.7 core and offender clauses give a faithful FF action on
Ω₁Z(O₂(LR)). Its simple normal component has two-group quotient and trivial
centralizer. It therefore lies in the actual offender subgroup, where the
full known-simple B.5.1 theorem applies. All six module conclusions and the
literal subgroup inclusion are retained. The model is transported back to
the original component quotient for both exchanged and Held branches.

No C.2.7 classification or action-generation premise is supplied.
Source: Aschbacher--Smith B.5.1 and C.2.7, pp.99--103,145--146; 15.4.20.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
open SL3Geometry.SourceCases
open TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {H U K K₁ : Subgroup G} {r : G}

private theorem model_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : QuasisimpleModel A) : QuasisimpleModel B := by
  cases h with
  | linearTwo F f => exact .linearTwo F (e.symm.trans f)
  | linearThree F f => exact .linearThree F (e.symm.trans f)
  | symplecticFour F f => exact .symplecticFour F (e.symm.trans f)
  | g2 F f => exact .g2 F (e.symm.trans f)
  | alternatingSix f => exact .alternatingSix (e.symm.trans f)
  | alternatingSeven f => exact .alternatingSeven (e.symm.trans f)
  | tripleSix c f =>
    exact .tripleSix ((Subgroup.centerCongr e.symm).trans c)
      ((QuotientGroup.congr _ _ e.symm (map_center_equiv e.symm)).trans f)
  | g2DerivedTwo f => exact .g2DerivedTwo (e.symm.trans f)
  | linearFourTwo f => exact .linearFourTwo (e.symm.trans f)
  | linearFiveTwo f => exact .linearFiveTwo (e.symm.trans f)

private theorem model_of_ff_conclusion
    {A W : Type u} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (C : Subgroup A)
    (hc : C ≤ offenderSubgroup ρ)
    (h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (C.subgroupOf (offenderSubgroup ρ))) :
    QuasisimpleModel C :=
  model_transport (subgroupOfEquivOfLe hc)
    ((SourceB5.quasisimpleConclusion h).clause_one.model _)

theorem source_star_ff_classification
    (h : Input d i j H U K) (L : Subgroup H)
    (hc : ComponentHypotheses KnownSimple.IsKnownSimple H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) L)
    (hr : IsPRadical 2 (((sourceRadical d U).subgroupOf H).subgroupOf
      (L ⊔ (sourceRadical d U).subgroupOf H)))
    [IsSimpleGroup (starComponent L ((sourceRadical d U).subgroupOf H))]
    [IsQuasisimple (starComponent L ((sourceRadical d U).subgroupOf H))] :
    let R := (sourceRadical d U).subgroupOf H
    let J := offenderSubgroup (starRepresentation L R)
    starComponent L R ≤ J ∧
    Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((starRepresentation L R).comp J.subtype) ((starComponent L R).subgroupOf J)) := by
  let R := (sourceRadical d U).subgroupOf H
  let D := L ⊔ R
  let C := starComponent L R
  have hco := source_component_core_offenders_of_local_radical h L KnownSimple.IsKnownSimple hc hr
  have hk : starKernel L R = pCore 2 D :=
    (h.local_module_comparison L hc.normalized hr).2.2.2.2
  let : (L.subgroupOf D).Normal := hc.local_normal
  let : C.Normal := (inferInstance : (L.subgroupOf D).Normal).map
    (starProjection L R) (QuotientGroup.mk'_surjective _)
  have hgen : C ⊔ starRadical L R = ⊤ := by
    change (L.subgroupOf D).map (starProjection L R) ⊔
      (R.subgroupOf D).map (starProjection L R) = ⊤
    rw [← Subgroup.map_sup]
    have htop : L.subgroupOf D ⊔ R.subgroupOf D = ⊤ := by
      rw [← subgroupOf_sup le_sup_left le_sup_right]
      exact subgroupOf_self _
    rw [htop]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hquot : IsPGroup 2 (Star L R ⧸ C) :=
    isPGroup_quotient_of_sup_eq_top C (starRadical L R)
      (hr.isPGroup.map (starProjection L R)) hgen
  have hC : centralizer (C : Set (Star L R)) = ⊥ :=
    centralizer_eq_bot_of_simple_two_quotient C (Group.IsPerfect.not_isMulCommutative C)
      hquot hco.1.2.2.2
  have hsD : IsSQTK KnownSimple.IsKnownSimple D := hc.sqtk.subgroup _
  have hsQ : IsSQTK KnownSimple.IsKnownSimple (D ⧸ pCore 2 D) := by
    refine ⟨?_, hsD.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsD.stronglyQuasithin p hp ho)
  have hs : IsSQTK KnownSimple.IsKnownSimple (Star L R) :=
    (IsSQTK.equiv (QuotientGroup.quotientMulEquivOfEq hk)).mpr hsQ
  exact ChapterB.QuasisimpleSource.SourceCompletion.ff_socle_source_conclusion
    (starRepresentation L R) C hC (hs.subgroup _)
    (NormalElementaryQuotient.representation_injective _ _ _ _) hco.2.2.1

theorem source_selected_ff_classification
    (h : Input d i j H U K) (s : Selected H U K K₁ r)
    (hc : ComponentHypotheses KnownSimple.IsKnownSimple H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) (K₁.subgroupOf H)) :
    let L := K₁.subgroupOf H
    let R := (sourceRadical d U).subgroupOf H
    let J := offenderSubgroup (starRepresentation L R)
    starComponent L R ≤ J ∧
    Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((starRepresentation L R).comp J.subtype) ((starComponent L R).subgroupOf J)) := by
  have hr := source_local_radical h s hc.normalized
  let e := SL3Geometry.source_componentStarEquiv h s hc.normalized hr
  let := hc.quasisimple
  let : IsQuasisimple (K₁ ⧸ pCore 2 K₁) :=
    IsQuasisimple.of_mulEquiv s.internalQuotientEquiv.symm
  let : IsSimpleGroup (K₁ ⧸ pCore 2 K₁) :=
    EmbeddingReduction.swapped_model_simple inferInstance s.model
  let : IsQuasisimple (starComponent (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup (starComponent (K₁.subgroupOf H) ((sourceRadical d U).subgroupOf H)) :=
    e.symm.isSimpleGroup
  exact source_star_ff_classification h _ hc hr

theorem source_held_ff_classification
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : Input d i j H U K)
    (unique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      d.wholeX ⊔ (d.T : Subgroup G) ≤ N → N = d.M₁)
    (hK : (K.subgroupOf H).IsCComponent)
    (hq : IsQuasisimple (Chapter1.XiQuotient K))
    (eH : Chapter1.XiQuotient K ≃* Held.He) :
    let L := K.subgroupOf H
    let R := (sourceRadical d U).subgroupOf H
    let J := offenderSubgroup (starRepresentation L R)
    starComponent L R ≤ J ∧
    Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((starRepresentation L R).comp J.subtype) ((starComponent L R).subgroupOf J)) := by
  have hc := single_component_hypotheses hG h unique hK hq
  let e := single_componentStarEquiv h hK
  let := hq
  let : IsSimpleGroup (Chapter1.XiQuotient K) :=
    EmbeddingReduction.simple_of_quasisimple_center_bot hq (by
      apply bot_unique
      intro z hz
      have hzm := (Subgroup.centerCongr eH) ⟨z,hz⟩ |>.property
      change eH z ∈ center Held.He at hzm
      rw [Held.LocalPairs.center_eq_bot, mem_bot] at hzm
      exact mem_bot.mpr (eH.injective (hzm.trans (map_one eH).symm)))
  let : IsQuasisimple (starComponent (K.subgroupOf H) ((sourceRadical d U).subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup (starComponent (K.subgroupOf H) ((sourceRadical d U).subgroupOf H)) :=
    e.symm.isSimpleGroup
  exact source_star_ff_classification h _ hc (single_local_radical h)

theorem source_selected_ff_model
    (h : Input d i j H U K) (s : Selected H U K K₁ r)
    (hc : ComponentHypotheses KnownSimple.IsKnownSimple H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) (K₁.subgroupOf H)) :
    QuasisimpleModel (Chapter1.XiQuotient K₁) := by
  obtain ⟨hle,⟨conclusion⟩⟩ := source_selected_ff_classification h s hc
  exact model_transport
    (SL3Geometry.source_componentStarEquiv h s hc.normalized
      (source_local_radical h s hc.normalized)).symm
    (model_of_ff_conclusion _ _ hle conclusion)

theorem source_held_ff_model
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : Input d i j H U K)
    (unique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      d.wholeX ⊔ (d.T : Subgroup G) ≤ N → N = d.M₁)
    (hK : (K.subgroupOf H).IsCComponent)
    (hq : IsQuasisimple (Chapter1.XiQuotient K))
    (eH : Chapter1.XiQuotient K ≃* Held.He) : QuasisimpleModel Held.He := by
  obtain ⟨hle,⟨conclusion⟩⟩ := source_held_ff_classification hG h unique hK hq eH
  exact model_transport ((single_componentStarEquiv h hK).symm.trans eH)
    (model_of_ff_conclusion _ _ hle conclusion)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly

