module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.Centralizers

/-!
# The literal neighboring quotient actors in DGS 9.3

Conjugation by V_v on V_w has kernel V_v intersect Q_w, using the
centralizer identity and the source trivial-displacement assumption.
The first isomorphism theorem identifies its actual image with the
source actor quotient and retains the formula on every representative.
Escape makes the image nontrivial. Applied in both directions, the
centralizer indices yield the strict square comparison in one direction.

This prepares the actual actors for corrected 5.12. It does not supply
the natural module, fixed-space generation on V/C_V(O²(L)), or the
Chapter 8 exchange used to establish the reverse source hypothesis.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, 9.2--9.3, printed p.142.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- Conjugation by the original neighboring span on the opposite span. -/
def neighborAction [∀ i, Finite (F i)] (hgen : F false ⊔ F true = ⊤)
    (v w : Vertex F) (hd : (graph F).dist v w + 1 ≤ b F) : V F v 1 →* MulAut (V F w 1) :=
  (V F w 1).normalizerMonoidHom.comp
    (inclusion ((V_le_stabilizer F hgen v w hd).trans (stabilizer_normalizes_V F w 1)))

/-- The original ambient element acts by its literal conjugation formula. -/
theorem neighborAction_apply [∀ i, Finite (F i)] (hgen : F false ⊔ F true = ⊤)
    (v w : Vertex F) (hd : (graph F).dist v w + 1 ≤ b F)
    (x : V F v 1) (z : V F w 1) :
    (neighborAction F hgen v w hd x z : G) = (x : G) * z * (x : G)⁻¹ := rfl

/-- Normality is inside the actual neighboring actor, not the completion. -/
theorem neighborCoreInter_normal (hgen : F false ⊔ F true = ⊤)
    (v w : Vertex F) (hd : (graph F).dist v w + 1 ≤ b F) :
    ((Q F w).subgroupOf (V F v 1)).Normal :=
  normal_subgroupOf_of_le_normalizer
    ((V_le_stabilizer F hgen v w hd).trans (stabilizer_normalizes_Q F w))

variable {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable (h : LocallyRankOneTriple P B)
variable (hS : ∀ v : Vertex (family P), ∃ T : Sylow 2 (U (family P) v),
      (T : Subgroup (U (family P) v)).map (U (family P) v).subtype = Q (family P) v)
variable (v w : Vertex (family P)) (hb : 1 < b (family P))
variable (hd : (graph (family P)).dist v w + 1 ≤ b (family P))
variable (hc : ⁅V (family P) v 1 ⊓ Q (family P) w, V (family P) w 1⁆ = ⊥)

section Critical
include hS hb hc

/-- The action kernel is precisely the opposite core pulled back to the actor. -/
theorem neighborAction_ker :
    letI := finite_endpoints h
    (neighborAction (family P) h.generate v w hd).ker = (Q (family P) w).subgroupOf (V (family P) v 1) := by
  let := finite_endpoints h
  have he := congrArg (fun A : Subgroup G => A.subgroupOf (V (family P) v 1))
    (neighbor_span_centralizer_eq_core_inter h hS v w hb hd hc)
  simp only [inf_subgroupOf_left] at he
  rw [← he]
  unfold neighborAction
  rw [← MonoidHom.comap_ker, normalizerMonoidHom_ker]
  rfl

/-- The source core index measures the image of the literal conjugation action. -/
theorem neighborAction_range_card :
    letI := finite_endpoints h
    Nat.card (neighborAction (family P) h.generate v w hd).range =
      (Q (family P) w).relIndex (V (family P) v 1) := by
  let := finite_endpoints h
  rw [← index_ker, neighborAction_ker h hS v w hb hd hc]
  rfl

/-- The source quotient is the actual action image, with every representative retained. -/
theorem neighborAction_quotient_equiv :
    letI := finite_endpoints h
    letI := neighborCoreInter_normal (family P) h.generate v w hd
    ∃ e : (V (family P) v 1 ⧸ (Q (family P) w).subgroupOf (V (family P) v 1)) ≃*
        (neighborAction (family P) h.generate v w hd).range,
      ∀ x : V (family P) v 1,
        (e (QuotientGroup.mk' _ x) : MulAut (V (family P) w 1)) =
          neighborAction (family P) h.generate v w hd x := by
  let := finite_endpoints h
  let := neighborCoreInter_normal (family P) h.generate v w hd
  let f := neighborAction (family P) h.generate v w hd
  let e := (QuotientGroup.quotientMulEquivOfEq (neighborAction_ker h hS v w hb hd hc).symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  refine ⟨e, ?_⟩
  intro x
  dsimp only [e, MulEquiv.trans_apply]

  rfl


/-- Critical escape gives a nontrivial action, rather than a formal quotient tag. -/
theorem neighborAction_range_one_lt (he : ¬ V (family P) v 1 ≤ Q (family P) w) :
    letI := finite_endpoints h
    1 < Nat.card (neighborAction (family P) h.generate v w hd).range := by
  let := finite_endpoints h
  rw [neighborAction_range_card h hS v w hb hd hc]
  have hv : V (family P) v 1 ≤ stabilizer (family P) v :=
    V_le_stabilizer (family P) h.generate v v (by simp only [SimpleGraph.dist_self, zero_add]; omega)
  let : Finite (V (family P) v 1) := Finite.of_injective (inclusion hv) (inclusion_injective _)
  change 1 < ((Q (family P) w).subgroupOf (V (family P) v 1)).index
  apply one_lt_index_of_ne_top
  exact fun hh => he (subgroupOf_eq_top.mp hh)


/-- The two nontrivial reciprocal actors force one of the strict square comparisons used in 9.3. -/
theorem mutual_neighbor_strict_bound
    (hr : ⁅V (family P) w 1 ⊓ Q (family P) v, V (family P) v 1⁆ = ⊥)
    (hev : ¬ V (family P) v 1 ≤ Q (family P) w)
    (hew : ¬ V (family P) w 1 ≤ Q (family P) v) :
    letI := finite_endpoints h
    let hd' : (graph (family P)).dist w v + 1 ≤ b (family P) := by rwa [SimpleGraph.dist_comm]
    (centralizer (V (family P) w 1 : Set G)).relIndex (V (family P) v 1) <
        Nat.card (neighborAction (family P) h.generate w v hd').range ^ 2 ∨
      (centralizer (V (family P) v 1 : Set G)).relIndex (V (family P) w 1) <
        Nat.card (neighborAction (family P) h.generate v w hd).range ^ 2 := by
  let := finite_endpoints h
  dsimp only
  have hd' : (graph (family P)).dist w v + 1 ≤ b (family P) := by rwa [SimpleGraph.dist_comm]
  have ha := neighborAction_range_one_lt h hS v w hb hd hc hev
  have hb' := neighborAction_range_one_lt h hS w v hb hd' hr hew
  have hv := congrArg (fun A : Subgroup G => A.relIndex (V (family P) v 1))
    (neighbor_span_centralizer_eq_core_inter h hS v w hb hd hc)
  have hw := congrArg (fun A : Subgroup G => A.relIndex (V (family P) w 1))
    (neighbor_span_centralizer_eq_core_inter h hS w v hb hd' hr)
  simp only [inf_relIndex_left] at hv hw
  rw [neighborAction_range_card h hS v w hb hd hc] at ha
  rw [neighborAction_range_card h hS w v hb hd' hr] at hb'
  rw [hv, hw, neighborAction_range_card h hS v w hb hd hc,
    neighborAction_range_card h hS w v hb hd' hr]
  rcases le_total ((Q (family P) w).relIndex (V (family P) v 1))
      ((Q (family P) v).relIndex (V (family P) w 1)) with hle | hle
  · left; nlinarith
  · right; nlinarith

end Critical
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
