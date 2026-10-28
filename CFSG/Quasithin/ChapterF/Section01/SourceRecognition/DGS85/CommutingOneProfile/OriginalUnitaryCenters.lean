module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalUnitaryInitial
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryCenterOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryPathValences

/-!
# Original unitary centers and field parameters

The short-path unitary profile applies to the literal reduced family coming
from the original Chapter 11 hypotheses. It transports the neighboring-core
identity, the beta and alpha center orders, and the alpha PSL₂ marking through
the full-Borel inclusion. The same marked field then determines every original
graph valence.

Only the source hypotheses and the beta PSU/SU marking are used here; no
four-walk transitivity premise is needed. This module is the consumer for the
three-walk center and field calculation, while the older path-profile APIs keep
their explicit four-walk premise.
Source: DGS85, *Groups and Graphs*, (11.6)(c,d), pp.172--174.
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

/-- The original neighboring-core identity and both center orders, together
with the alpha marking over the square of the supplied beta field. -/
theorem original_unitary_centers_and_field :
    (neighborCoreIntersection F₀ (base F₀ true)).map (G₀).subtype =
      (Z F₀ (base F₀ true)).map (G₀).subtype ∧
    Nat.card ((Z F₀ (base F₀ true)).map (G₀).subtype) = 2^m ∧
    Nat.card ((Z F₀ (base F₀ false)).map (G₀).subtype) = 2^(4*m) ∧
    ClassicalGroup.IsPSL ((graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype)) 2 (2^(2*m)) := by
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
  have hs := source_unitary_marked_center_profile
    (P := fun i => (P₀ L₀ S₀ i).subgroupOf G₀) (B := (B₀ L₀ S₀).subgroupOf G₀)
    (a := base F₀ false) (b := base F₀ true)
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h)
    d hc hb hcomm ma hm mark'
  change neighborCoreIntersection F₀ (base F₀ true) = Z F₀ (base F₀ true) ∧
    Nat.card (Z F₀ (base F₀ true)) = 2^m ∧
    Nat.card (Z F₀ (base F₀ false)) = 2^(4*m) ∧
    ClassicalGroup.IsPSL (d.localGroup (base F₀ false) ⧸
      pCore 2 (d.localGroup (base F₀ false))) 2 (2^(2*m)) at hs
  refine ⟨congrArg (Subgroup.map (G₀).subtype) hs.1,?_,?_,?_⟩
  · simpa only [card_map_of_injective (G₀).subtype_injective] using hs.2.1
  · simpa only [card_map_of_injective (G₀).subtype_injective] using hs.2.2.1
  · exact hs.2.2.2.of_mulEquiv eqa.symm

/-- The marked alpha field and every original graph valence, with no path
transitivity premise. -/
theorem original_unitary_field_and_valences :
    ClassicalGroup.IsPSL ((graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype)) 2 (2^(2*m)) ∧
      ∀ x : Vertex F₀, Nat.card ((graph F₀).neighborSet x) =
        2^(if x.type then 3*m else 2*m)+1 := by
  have ha := (original_unitary_centers_and_field h hc hb hcomm Ma hm mark).2.2.2
  exact ⟨ha,original_reduced_unitary_neighbor_cards h (reducedFullEarlierLocalTheorems h) hm ha mark⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
