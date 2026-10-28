module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFullMiddleCenter
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.Twisted

/-!
# The original left A5 quotient kills full middle central involutions

The literal reduced Borel index is five, so the source-constructed natural
alpha field has four elements. Its actual cubic edge actor excludes every
central involution of the full middle stabilizer. The right quotient is
arbitrary and no native comparison is assumed.
-/

public noncomputable section
open Subgroup Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
variable {G : Type*} [Group G] [Finite G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S

/-- A single original A5 marking suffices for the distance-two full middle
central involution obstruction. -/
theorem original_a5_bTwo_middle_central_involution_eq_one
    (h : HypothesisF11 L S)
    (a : (L 0 ⧸ pCore 2 (L 0)) ≃* alternatingGroup (Fin 5))
    {w : Vertex F} (hc : IsCriticalPair F (base F false) w)
    (hne : ⁅Z F (base F false),Z F w⁆ ≠ ⊥)
    (hb : b F = 2) (hmw : (graph F).Adj (base F true) w)
    (x : G₀ L S)
    (hx : x ∈ (center (stabilizer F (base F true))).map
      (stabilizer F (base F true)).subtype) (hx2 : x^2 = 1) : x = 1 := by
  have hvm : (graph F).Adj (base F false) (base F true) :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨k,_,_,_,_,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hvm hmw
  have hi := c.neighbor_card (reduced_triple h)
  change Nat.card ((graph F).neighborSet (base F false)) = Nat.card k + 1 at hi
  rw [card_neighbor_base] at hi
  change ((P₀ L S 1).subgroupOf (G₀ L S)).relIndex
    ((P₀ L S 0).subgroupOf (G₀ L S)) = _ at hi
  rw [←inf_relIndex_left,(reduced_triple h).intersection,
    relIndex_subgroupOf (show P₀ L S 0 ≤ G₀ L S from le_sup_left),
    B₀_eq_source h,P₀_eq_source h 0,
    A5PairCatalogue.borel_index (SuzukiContainment.reduced_hypothesis h) 0 a] at hi
  exact c.full_middle_central_involution_eq_one (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hactor
    (reduced_bTwo_middle_central h hc hne hb hvm hmw) (by omega) x hx hx2

end CFSG.Quasithin.ChapterF.Source
