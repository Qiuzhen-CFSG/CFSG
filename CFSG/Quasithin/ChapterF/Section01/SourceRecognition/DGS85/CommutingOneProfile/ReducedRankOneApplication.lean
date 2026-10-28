module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.RankOneSeparation

/-!
# General Chapter 11 seeds in the original reduced completion

The original F1.11 reduction supplies the full two-closed Borel and the
normal Sylow of each local kernel. Thus the general (11.2)(c) seed escapes
the full opposite kernel, and its opposite-edge generation transports under
the original completion inclusion. The exact (11.3)(h) core-generation and
(11.4) core-product identities also supply the (11.5) supplement, discharging
that premise in the (11.6) transitivity and separation applications. The
separation equality is retained in both the reduced and original completion.

Earlier local-group and actual quotient-model inputs remain with the shared
Chapter 6 producer. The two Chapter 11 core identities remain obligations
of this source family; the full (11.7)--(11.8) profiles are not concluded.
No kernel/core identification or marked amalgam comparison is inferred.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.2)(c), p.168; (11.3)--(11.6), pp.168--174; the reduction, pp.95--96.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L S
local notation "G₀" => Reduction.G₀ L S

/-- The general (11.2)(c) application on the actual reduced F1.11 graph.
 The seed escapes the full kernel as well as the two-core. -/
theorem reduced_rankOne_seed_escape (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (M : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b))) :
    ¬ IsPGroup 2 (Z F₀ a ⊔ Z F₀ c : Subgroup G₀) ∧
      (¬ Z F₀ a ⊓ Q F₀ b ≤ U F₀ c) ∧ ⁅Z F₀ a ⊓ Q F₀ b,Z F₀ c⁆ ≠ ⊥ := by
  let ht := Reduction.reduced_triple h
  let : ∀ i, Finite (F₀ i) := finite_endpoints ht
  let : IsElementaryAbelian 2 (Z F₀ a) := source_center_elementary ht a
  let : IsElementaryAbelian 2 (Z F₀ a ⊓ Q F₀ b : Subgroup G₀) :=
    IsElementaryAbelian.of_le inf_le_left
  have hs := source_rankOne_seed_escape ht (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac M
  refine ⟨source_rankOne_centers_not_isPGroup ht (Reduction.reduced_borel_core_sylow h)
    d hc hb hbc hac M,?_,hs.2⟩
  intro he
  have heQ : Z F₀ a ⊓ Q F₀ b ≤ Q F₀ c := pSubgroup_le_Q_of_le_U F₀ c _
    (IsElementaryAbelian.isPGroup 2 (Z F₀ a ⊓ Q F₀ b : Subgroup G₀)) he
    (Reduction.reduced_kernel_sylow h c)
  exact hs.1 heQ

/-- The opposite-edge generation formula uses the original inclusion of the
 reduced completion, with the same seeds and the embedded full-edge radical. -/
theorem reduced_rankOne_seed_generation_original (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c w : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (hcw : (graph F₀).Adj c w) (hbw : b ≠ w)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (Mc : IsRankOneModel (d.localGroup c ⧸ pCore 2 (d.localGroup c))) :
    ((Z F₀ a).map (G₀).subtype ⊓ (Q F₀ b).map (G₀).subtype) ⊔
      ((stabilizer F₀ c).map (G₀).subtype ⊓ (stabilizer F₀ w).map (G₀).subtype).pCoreIn 2 =
        (d.localGroup c).map (G₀).subtype := by
  have hh := source_rankOne_seed_edge_generation (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac hcw hbw Mb Mc
  have hm := congrArg (Subgroup.map (G₀).subtype) hh
  rwa [Subgroup.map_sup,Subgroup.map_inf _ _ _ (G₀).subtype_injective,
    map_pCoreIn_of_injective 2 _ _ (G₀).subtype_injective,
    Subgroup.map_inf _ _ _ (G₀).subtype_injective] at hm

/-- The (11.3)(h) core generation and (11.4) core product imply the entire
 opening separation argument of (11.6) on the same reduced graph. The
 (11.5) supplement, opposite-seed transitivity and faithful vanishing are
 all discharged here. Earlier local and rank-one inputs remain explicit. -/
theorem reduced_rankOne_neighbor_separation (h : HypothesisF11 L S)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hproduct : (stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2 = Q F₀ a ⊔ Q F₀ b)
    (hcore : Q F₀ b = pairSpan (Z F₀ a) (Z F₀ c) (Q F₀ b) ⊔ (Q F₀ a ⊓ Q F₀ b))
    (g : G₀) (hga : g ∈ stabilizer F₀ a) (hgb : g • b ≠ b) :
    (∀ v, (graph F₀).Adj a v →
      ∃ w ∈ (Z F₀ c ⊓ Q F₀ b) ⊔ (Z F₀ (g • c) ⊓ Q F₀ (g • b)), w • b = v) ∧
      neighborCoreIntersection F₀ b ⊓ Q F₀ (g • c) = ⊥ ∧
      (neighborCoreIntersection F₀ b).map (G₀).subtype ⊓ (Q F₀ (g • c)).map (G₀).subtype = ⊥ := by
  let ht := Reduction.reduced_triple h
  have hsupp : (stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2 =
      (Z F₀ c ⊓ Q F₀ b) ⊔ Q F₀ a := by
    rw [sup_comm]
    exact alpha_supplement_of_pair_generation _ _ _ _ _ hproduct hcore
      ((source_Z_Q_U ht a).1.trans (map_subtype_le _))
  have hsep := source_rankOne_neighbor_intersection_separated ht
    (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac Ma Mb hsupp g hga hgb
  refine ⟨fun v hv => source_rankOne_opposite_seed_transitive ht
    (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac Ma Mb hsupp g hga hgb hv,hsep,?_⟩
  change neighborCoreIntersection F₀ b ⊓ Q F₀ (g • c) = ⊥ at hsep
  rw [←Subgroup.map_inf _ _ _ (G₀).subtype_injective,hsep,Subgroup.map_bot]
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
