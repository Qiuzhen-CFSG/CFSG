module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairCoreQuotient

/-!
# Original-source applications of the general two-seed section

The reduced F1.11 geometry supplies the literal Chapter 11 section with
no alpha row selected. Both earlier quotient markings may be supplied
on their images in the original completion; their induced two-core
quotient isomorphisms pull them back to the same local actors.

The original reduced-group inclusion transports the core containment,
exact intersection and both commutator bounds. Thus the module and its
source geometry refer to the same subgroups, including for an infinite
original completion. General alpha selection, (11.3)(h)/(11.4), nonlinear
profiles, path parameters and final marked assembly remain obligations.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3), printed pp.168--171; source reduction, pp.95--96.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G]
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L S
local notation "G₀" => Reduction.G₀ L S

/-- The actual module in the reduced F1.11 geometry, with both quotient
markings supplied on their images in the original completion. -/
theorem original_reduced_rankOne_pair_section (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype))) :
    let H := (Z F₀ a ⊔ Z F₀ c) ⊔ Q F₀ b
    let V := pairSpan (Z F₀ a) (Z F₀ c) (Q F₀ b)
    let J := Z F₀ a ⊓ Z F₀ c
    ∃ hJ : (J.subgroupOf V).Normal, letI := hJ
      ∃ hE : IsElementaryAbelian 2 (V ⧸ J.subgroupOf V), letI := hE
        ∃ hQ : ((Q F₀ b).subgroupOf H).Normal, letI := hQ
          let π := QuotientGroup.mk' ((Q F₀ b).subgroupOf H)
          ∃ σ : Representation (ZMod 2) (H ⧸ (Q F₀ b).subgroupOf H)
              (Additive (V ⧸ J.subgroupOf V)),
            ∃ s : BinaryConjugationSection H V J (σ.comp π),
              (∀ x : V, (s.coordinates x).toAdd =
                Additive.ofMul (QuotientGroup.mk' (J.subgroupOf V) x)) ∧
              IsCompl (s.imageSpace (Z F₀ a ⊓ Q F₀ b)) (s.imageSpace (Z F₀ c ⊓ Q F₀ b)) ∧
              IsQuadratic σ (((Z F₀ a).subgroupOf H).map π) ∧
              GeneratedByFixedSpace σ (((Z F₀ a).subgroupOf H).map π) := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  exact source_rankOne_pair_section (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb)

/-- The same source core, seed intersection and action bounds in the original
completion. All images use the literal reduced-group inclusion. -/
theorem original_reduced_rankOne_pair_geometry (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype))) :
    let j := (G₀).subtype
    let D := (Q F₀ a ⊓ Q F₀ c).map j
    let V := (pairSpan (Z F₀ a) (Z F₀ c) (Q F₀ b)).map j
    D ≤ (Q F₀ b).map j ∧ D ⊓ V = (Z F₀ a).map j ⊓ (Z F₀ c).map j ∧
      ⁅(Q F₀ b).map j,V⁆ ≤ D ∧
      (Z F₀ a).map j ⊔ (Z F₀ c).map j ≤ centralizer (D : Set G) ∧
      ⁅(Q F₀ b).map j,(Z F₀ a).map j ⊔ (Z F₀ c).map j⁆ ≤ V := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have Ma₀ := Ma.of_equiv eqa
  have Mb₀ := Mb.of_equiv eqb
  have ht := Reduction.reduced_triple h
  have hB := Reduction.reduced_borel_core_sylow h
  have hab := source_critical_one_adjacent hc hb
  have hn := source_pair_core_normalizers ht hab hbc
  dsimp only
  refine ⟨map_mono (source_rankOne_pair_core_le_beta ht hB d hab hbc hac Mb₀),?_,?_,?_,?_⟩
  · rw [←map_inf _ _ _ (G₀).subtype_injective,←map_inf _ _ _ (G₀).subtype_injective]
    exact congrArg (map (G₀).subtype) (source_rankOne_pair_core_intersection ht hB d hc hb hbc hac Mb₀)
  · rw [←map_commutator]
    exact map_mono (source_rankOne_pair_core_action ht hB d hc hb hbc Ma₀ Mb₀)
  · rw [←Subgroup.map_sup]
    apply commutator_eq_bot_iff_le_centralizer.mp
    have he : ⁅Z F₀ a ⊔ Z F₀ c,Q F₀ a ⊓ Q F₀ c⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr hn.1
    rw [←map_commutator,he,Subgroup.map_bot]
  · rw [←Subgroup.map_sup,←map_commutator]
    exact map_mono hn.2.2.2

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
