module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalUnitaryCenters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryMarkedCoreOrders

/-!
# The original unitary core orders without four-walk transitivity

The canonical earlier-local data and marked short-path calculation give all
core orders in the reduced family. Injectivity transports their cardinalities
and relative indices to the original group. At the base edge the transported
edge two-core is exactly O₂ of the full original common Borel.

The alpha catalogue and the supplied positive PSU3/SU3 degree are retained.
No path action, escape, or nonelementarity premise is added. The compatibility
consumer in OriginalUnitarySource keeps its historical signature and uses
this stronger result. Natural alpha coordinates and the longer path profile
remain separate obligations.
Source: DGS85, Groups and Graphs, (11.8)(d,f), pp.175--176; reduction pp.95--96.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open CommutingNontrivial NoncommutingProfile Subgroup.CosetGeometry.RankTwo Reduction
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

variable (h : HypothesisF11 L₀ S₀)
    (hc : IsCriticalPair (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false) (base (Reduction.reducedFamily L₀ S₀) true))
    (hb : DGS85.b (Reduction.reducedFamily L₀ S₀) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false),Z (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)⁆ = ⊥)
    (Ma : IsRankOneModel ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false)).map ((Reduction.G₀ L₀ S₀)).subtype ⧸
      pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) false)).map ((Reduction.G₀ L₀ S₀)).subtype)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype ⧸
        pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype)) 3 (2^m) ∨
      IsSU ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype ⧸
        pCore 2 ((graphLocalGroup (Reduction.reducedFamily L₀ S₀) (base (Reduction.reducedFamily L₀ S₀) true)).map ((Reduction.G₀ L₀ S₀)).subtype)) 3 (2^m))

include h hc hb hcomm Ma hm mark

/-- Both vertex-core orders, the full Borel two-core order, and the alpha
central index, from the original source hypotheses and supplied unitary marking. -/
theorem original_borel_unitary_core_orders_from_marking :
    Nat.card ((Q F₀ (base F₀ true)).map (G₀).subtype) = 2^(7*m) ∧
      Nat.card (twoCore (commonBorel L₀ S₀)) = 2^(10*m) ∧
      Nat.card ((Q F₀ (base F₀ false)).map (G₀).subtype) = 2^(8*m) ∧
      ((Z F₀ (base F₀ false)).map (G₀).subtype).relIndex
        ((Q F₀ (base F₀ false)).map (G₀).subtype) = 2^(4*m) := by
  let d := reducedFullEarlierLocalTheorems h
  let ea := (d.localGroup (base F₀ false)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup (base F₀ true)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have ma : IsRankOneModel (d.localGroup (base F₀ false) ⧸
      pCore 2 (d.localGroup (base F₀ false))) := by
    exact Ma.of_equiv eqa
  have mark' : ClassicalGroup.IsPSU (d.localGroup (base F₀ true) ⧸
      pCore 2 (d.localGroup (base F₀ true))) 3 (2^m) ∨
      IsSU (d.localGroup (base F₀ true) ⧸
        pCore 2 (d.localGroup (base F₀ true))) 3 (2^m) := by
    rcases mark with hh | ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩
    · exact Or.inl (hh.of_mulEquiv eqb)
    · exact Or.inr ⟨E,inferInstance,inferInstance,J,hcard,hconj,⟨eqb.trans e⟩⟩
  obtain ⟨c,hbc,hac,g,hga,hgb,hesc,p,hp,hpv⟩ :=
    source_unitary_beta_escaping_four_walk
      (P := fun i => (P₀ L₀ S₀ i).subgroupOf G₀) (B := (B₀ L₀ S₀).subgroupOf G₀)
      (a := base F₀ false) (b := base F₀ true)
      (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h)
      d hc hb hcomm ma hm mark'
  have hs := source_unitary_core_orders_from_marking
    (P := fun i => (P₀ L₀ S₀ i).subgroupOf G₀) (B := (B₀ L₀ S₀).subgroupOf G₀)
    (a := base F₀ false) (b := base F₀ true)
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h)
    d hc hb hcomm hbc hac ma hm mark'
  change (Z F₀ (base F₀ true)).relIndex (Q F₀ (base F₀ true)) = 2^(6*m) ∧
    Nat.card (Q F₀ (base F₀ true)) = 2^(7*m) ∧
    Nat.card ((stabilizer F₀ (base F₀ false) ⊓ stabilizer F₀ (base F₀ true)).pCoreIn 2) =
      2^(10*m) ∧ Nat.card (Q F₀ (base F₀ false)) = 2^(8*m) ∧
    (Z F₀ (base F₀ false)).relIndex (Q F₀ (base F₀ false)) = 2^(4*m) at hs
  let R := (stabilizer F₀ (base F₀ false) ⊓ stabilizer F₀ (base F₀ true)).pCoreIn 2
  have htr := Reduction.reduced_triple h
  have hBG : Reduction.B₀ L₀ S₀ ≤ G₀ :=
    (show Reduction.B₀ L₀ S₀ ≤ Reduction.P₀ L₀ S₀ 0 from le_sup_right).trans le_sup_left
  have hRG : twoCore (commonBorel L₀ S₀) ≤ G₀ :=
    (show twoCore (commonBorel L₀ S₀) ≤ Reduction.B₀ L₀ S₀ from le_sup_right).trans hBG
  have hmap : R.map (G₀).subtype = twoCore (commonBorel L₀ S₀) := by
    dsimp only [R]
    rw [show stabilizer F₀ (base F₀ false) = F₀ false from Subgroup.CosetGeometry.stabilizer_base _ _,
      show stabilizer F₀ (base F₀ true) = F₀ true from Subgroup.CosetGeometry.stabilizer_base _ _,
      show F₀ false ⊓ F₀ true = (Reduction.B₀ L₀ S₀).subgroupOf G₀ from htr.intersection,
      pCoreIn_subgroupOf 2 _ _ hBG,Reduction.B₀_core h]
    exact map_subgroupOf_eq_of_le hRG
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [card_map_of_injective (G₀).subtype_injective] using hs.2.1
  · rw [←hmap,card_map_of_injective (G₀).subtype_injective]
    exact hs.2.2.1
  · simpa only [card_map_of_injective (G₀).subtype_injective] using hs.2.2.2.1
  · simpa only [relIndex_map_map_of_injective _ _ (G₀).subtype_injective] using hs.2.2.2.2

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
