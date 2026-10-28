module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.RankOne.Geometry
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2BorelCentralizer
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2ThompsonBorel
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.AmbientLift

/-!
# The actual natural-block orbit Borel

The selected Sylow intersection identifies M_L with the full-cover Borel.
Its two-perfectness passes to the S-conjugate span B. A two-subgroup
centralizing B centralizes M_L, hence L, by the relative component theorem.
This retains the actual S-orbit; S need not normalize L.

The full-cover offender argument also gives Thompson normalization. These
discharge all three natural-block Borel clauses of15.1.21(i), including n=2.
The earlier15.1.14 residual premise stays in PreExclusionSource, with final
discharge at the pre-exclusion catalogue and large-action-exclusion owners.
Source: Aschbacher--Smith15.1.21, printed pp.1097--1098.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

private theorem natural_borel_sylow
    (s : d.PreExclusionSource h.normalized p) (r : d.ConstrainedRankOneAlternative) :
    ∃ P : Sylow 2 d.L, (P : Subgroup d.L).map d.L.subtype = d.SL ∧
      d.ML = (normalizer (P : Set d.L)).map d.L.subtype := by
  obtain ⟨P,hP⟩ := s.component_sylow
  have hP' : (P : Subgroup d.L) = d.SL.subgroupOf d.L := by
    apply map_injective d.L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le d.SL_le_L]
  refine ⟨P,hP,?_⟩
  change d.ML = (normalizer ((P : Subgroup d.L) : Set d.L)).map d.L.subtype
  rw [hP']
  exact r.borel

/-- The literal S-orbit Borel is two-perfect for every natural block, n=2 included. -/
theorem PreExclusionSource.rankOne_natural_borel_perfect
    (s : d.PreExclusionSource h.normalized p) (r : d.ConstrainedRankOneAlternative)
    {n : ℕ} (hb : ChapterC.IsL2EvenBlock d.L n) :
    IsPPerfect 2 d.rankOneBorelClosure := by
  obtain ⟨P,_,hP⟩ := natural_borel_sylow (h := h) s r
  have hp : IsPPerfect 2 d.ML := by
    rw [hP]
    exact (hb.borel_twoPerfect P).of_surjective
      (d.L.subtype.subgroupMap _) (d.L.subtype.subgroupMap_surjective _)
  exact ChapterC.RankOne.ChiProduct.conjugateSpan_twoPerfect d.ML d.S hp

/-- Centralizing the orbit Borel forces centralization of the original component. -/
theorem PreExclusionSource.rankOne_natural_borel_centralizers
    (s : d.PreExclusionSource h.normalized p) (r : d.ConstrainedRankOneAlternative)
    {n : ℕ} (hb : ChapterC.IsL2EvenBlock d.L n) :
    d.S ⊓ centralizer (d.rankOneBorelClosure : Set G) ≤
      d.S ⊓ centralizer (d.L : Set G) := by
  obtain ⟨P,_,hP⟩ := natural_borel_sylow (h := h) s r
  have hc := ChapterC.IsL2EvenBlock.relative_borel_centralizer d.G1 d.L d.S hb
    d.L_component.1 d.S_le_G1 d.L_component.2 (T.isPGroup'.to_le d.S_le_T) P
  rw [←hP] at hc
  exact le_inf inf_le_left
    ((inf_le_inf_left _ (centralizer_le (le_conjugateSpanBy d.ML d.S))).trans hc)

/-- Adapter retaining an explicit Thompson-normalization proof. -/
theorem PreExclusionSource.rankOne_natural_borel_geometry_of_thompson
    (s : d.PreExclusionSource h.normalized p) (r : d.ConstrainedRankOneAlternative)
    {n : ℕ} (hb : ChapterC.IsL2EvenBlock d.L n)
    (hth : d.rankOneBorelClosure ≤ normalizer (Stellmacher.elementaryAbelianMaxJ d.S : Set G)) :
    d.RankOneBorelGeometry :=
  ⟨s.rankOne_natural_borel_perfect (h := h) r hb,hth,
    s.rankOne_natural_borel_centralizers (h := h) r hb⟩

/-- The full natural-block Borel normalizes J(S), and so does its S-orbit span. -/
theorem PreExclusionSource.rankOne_natural_borel_thompson
    (s : d.PreExclusionSource h.normalized p) (r : d.ConstrainedRankOneAlternative)
    {n : ℕ} (hb : ChapterC.IsL2EvenBlock d.L n) :
    d.rankOneBorelClosure ≤ normalizer (Stellmacher.elementaryAbelianMaxJ d.S : Set G) := by
  obtain ⟨P,hP,hB⟩ := natural_borel_sylow (h := h) s r
  have hn := ChapterC.IsL2EvenBlock.borel_normalizes_thompson d.L d.S hb
    (T.isPGroup'.to_le d.S_le_T) P (by rw [hP]; exact d.SL_le_S)
    (le_normalizer_iff_commutator_le_left.mpr r.thompson.le)
  rw [←hB] at hn
  have hSJ : d.S ≤ normalizer (Stellmacher.elementaryAbelianMaxJ d.S : Set G) :=
    d.S.le_normalizer.trans (Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ d.S)
  exact conjugateSpanBy_le hn (hSJ.trans
    (normalizer (Stellmacher.elementaryAbelianMaxJ d.S : Set G)).le_normalizer)

/-- All three source Borel clauses for the literal orbit subgroup, n=2 included. -/
theorem PreExclusionSource.rankOne_natural_borel_geometry
    (s : d.PreExclusionSource h.normalized p) (r : d.ConstrainedRankOneAlternative)
    {n : ℕ} (hb : ChapterC.IsL2EvenBlock d.L n) : d.RankOneBorelGeometry :=
  s.rankOne_natural_borel_geometry_of_thompson (h := h) r hb
    (s.rankOne_natural_borel_thompson (h := h) r hb)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
