module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairFixedSpaces
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.CenterOmegaImage
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.GraphExclusions

/-!
# Original-source consumers of the general pair fixed spaces

The reduced F1.11 geometry constructs its edge Sylow and identifies the
critical-center image with the full omega-center in the actual beta
quotient. Quotient markings on the original local-group images pull back
through the isomorphisms induced by the reduced-group inclusion.

The same inclusion transports both exact fixed preimages and the zero
whole-pair fixed space. The exact alpha-core intersection then discharges
the intersection premise in the nonlinear small-core bound. Its edge-core
product, center and seed counts, and nonelementary S/Q_beta premise remain
explicit source obligations. This is not an unconditional Suzuki exclusion
or completion of (11.8); general alpha selection and marked assembly remain
with the Chapter 11 owner.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.2)(b), (11.3)(b), and the small-core argument in (11.8),
printed pp.168--171 and 175--176.
-/

public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G]
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L S
local notation "G₀" => Reduction.G₀ L S

/-- The source reduction supplies the actual edge Sylow and its full critical-center image. -/
theorem reduced_rankOne_center_image_omega (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1)
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype))) :
    ∃ T : Sylow 2 (d.localGroup b),
      (T : Subgroup (d.localGroup b)).map (d.localGroup b).subtype =
        (stabilizer F₀ b ⊓ stabilizer F₀ a).pCoreIn 2 ∧
      ((Z F₀ a).subgroupOf (d.localGroup b)).map (QuotientGroup.mk' (pCore 2 (d.localGroup b))) =
        omegaCenterIn ((T : Subgroup (d.localGroup b)).map
          (QuotientGroup.mk' (pCore 2 (d.localGroup b)))) := by
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have ht := Reduction.reduced_triple h
  have hB := Reduction.reduced_borel_core_sylow h
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow ht hB d (source_critical_one_adjacent hc hb).symm
  exact ⟨T,hT,source_rankOne_center_image_omega ht hB d hc hb (Mb.of_equiv eqb) T hT⟩

private theorem fixed_preimage_map {C D : Type*} [Group C] [Group D]
    (j : C →* D) (hj : Function.Injective j) (V J A E : Subgroup C)
    (h : ∀ x ∈ V, (∀ t ∈ A, ⁅x,t⁆ ∈ J) ↔ x ∈ E) :
    ∀ x ∈ V.map j, (∀ t ∈ A.map j, ⁅x,t⁆ ∈ J.map j) ↔ x ∈ E.map j := by
  rintro _ ⟨x,hx,rfl⟩
  have hm (K : Subgroup C) (y : C) : j y ∈ K.map j ↔ y ∈ K := by
    constructor
    · rintro ⟨z,hz,he⟩
      exact hj he ▸ hz
    · exact fun hy => mem_map_of_mem j hy
  rw [hm E x,←h x hx]
  constructor
  · intro hh t ht
    apply (hm J _).mp
    rw [map_commutatorElement]
    exact hh (j t) (mem_map_of_mem j ht)
  · intro hh t ht
    obtain ⟨t,ht,rfl⟩ := ht
    rw [←map_commutatorElement]
    exact mem_map_of_mem j (hh t ht)

/-- The exact source fixed preimages transported through the original reduced-group inclusion. -/
theorem original_reduced_rankOne_pair_fixed_preimages (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype))) :
    let j := (G₀).subtype
    let V := (pairSpan (Z F₀ a) (Z F₀ c) (Q F₀ b)).map j
    let J := (Z F₀ a).map j ⊓ (Z F₀ c).map j
    ∀ x ∈ V,
      ((∀ t ∈ (Z F₀ a).map j, ⁅x,t⁆ ∈ J) ↔ x ∈ (Z F₀ a).map j ⊓ (Q F₀ b).map j) ∧
      ((∀ t ∈ (Z F₀ c).map j, ⁅x,t⁆ ∈ J) ↔ x ∈ (Z F₀ c).map j ⊓ (Q F₀ b).map j) ∧
      ((∀ t ∈ (Z F₀ a).map j ⊔ (Z F₀ c).map j, ⁅x,t⁆ ∈ J) ↔ x ∈ J) := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have hs := source_rankOne_pair_fixed_preimages (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb)
  dsimp only
  rw [←map_inf _ _ _ (G₀).subtype_injective,←map_inf _ _ _ (G₀).subtype_injective,
    ←map_inf _ _ _ (G₀).subtype_injective,←Subgroup.map_sup]
  intro x hx
  exact ⟨fixed_preimage_map (G₀).subtype (G₀).subtype_injective _ _ _ _
      (fun x hx => (hs x hx).1) x hx,
    fixed_preimage_map (G₀).subtype (G₀).subtype_injective _ _ _ _
      (fun x hx => (hs x hx).2.1) x hx,
    fixed_preimage_map (G₀).subtype (G₀).subtype_injective _ _ _ _
      (fun x hx => (hs x hx).2.2) x hx⟩

/-- The general intersection calculation discharges the intersection premise
of the nonlinear small-core exclusion, in the original inclusion. -/
theorem original_reduced_rankOne_nonElementary_core_lower_bound (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)))
    (S₀ : Subgroup G₀) (hS : S₀ = Q F₀ a ⊔ Q F₀ b)
    (qα qβ : ℕ) (hqβ : 0 < qβ)
    (hZ : Nat.card (Z F₀ a) = qα * qβ ^ 2)
    (hindex : (Z F₀ a ⊓ Q F₀ b).relIndex (Z F₀ a) = qβ)
    (hinter : Nat.card ((Z F₀ a ⊓ Q F₀ b) ⊓ (Z F₀ c ⊓ Q F₀ b) : Subgroup G₀) = qβ)
    [((Q F₀ b).subgroupOf S₀).Normal]
    (hn : ¬ IsElementaryAbelian 2 (S₀ ⧸ (Q F₀ b).subgroupOf S₀)) :
    qα ^ 2 * qβ < Nat.card ((Q F₀ b).map (G₀).subtype) := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have ht := Reduction.reduced_triple h
  have hB := Reduction.reduced_borel_core_sylow h
  have hi := (source_rankOne_pair_core_seed_intersections ht hB d hc hb hbc hac
    (Ma.of_equiv eqa) (Mb.of_equiv eqb)).1.le.trans inf_le_left
  rw [card_map_of_injective (G₀).subtype_injective]
  exact source_nonElementary_beta_excludes_small_core ht (source_critical_one_adjacent hc hb)
    hbc S₀ hS hi qα qβ hqβ hZ hindex hinter hn

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
