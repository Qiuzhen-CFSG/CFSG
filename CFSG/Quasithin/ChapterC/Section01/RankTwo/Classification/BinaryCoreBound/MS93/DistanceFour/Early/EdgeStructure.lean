module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.OrderTwo

/-!
# Assembly of the binary edge calculations

The local arithmetic reduces all five EdgeFacts clauses to two remaining
source arguments: the containment (4.6.4), and exclusion of edge displacement
of order two in (4.6.5). The latter uses the source application of (2.3).
The constructor below retains both premises explicitly. It is a conditional
assembly lemma, not a proof of those source assertions from InitialFacts.

Source: Meierfrankenfeld--Stellmacher (1993), pp.902--903. The second assertion
printed as (4.6.6), derived noncentrality, belongs to the EarlyFacts owner.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Conditional assembly after the two source edge arguments have been supplied.
It computes the two indices from the actual natural and edge actions. -/
theorem edgeFacts_of_containment_of_not_two (common : CommonFacts R source geometry)
    (hcontain : ∀ a b, color R a = false → Adjacent R a b →
      ⁅Z R a, Q R b⁆ ≤ Z R b)
    (hnot_two : ∀ a b, color R a = false → Adjacent R a b →
      Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) ≠ 2) :
    EdgeFacts R := by
  have hcard (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b) :
      Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) = 4 :=
    (edge_commutator_card_two_or_four common a b ha hab (hcontain a b ha hab)).resolve_left
      (hnot_two a b ha hab)
  exact {
    edge_commutator_le_Z := hcontain
    commutator_le_Z := commutator_le_Z_of_edge common hcontain
    edge_commutator_card := hcard
    edge_Z_index := fun a b ha hab =>
      edge_Z_index_of_card common a b ha hab (hcontain a b ha hab) (hcard a b ha hab)
    edge_Q_index := fun a b ha hab =>
      edge_Q_index_of_card common a b ha hab (hcontain a b ha hab) (hcard a b ha hab) }

/-- Construct the binary edge facts from the distance-four source arguments.

The containment is the original (4.6.4) argument, while the order-two
exclusion is (4.6.5).  The preceding conditional assembly then computes the
order-four displacement and both relative indices, giving the first assertion
labeled (4.6.6). -/
theorem edgeFacts_of_initial (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (initial : InitialFacts R geometry) : EdgeFacts R := by
  have hcontain : ∀ a b, color R a = false → Adjacent R a b →
      ⁅Z R a, Q R b⁆ ≤ Z R b := by
    intro a b ha hab
    exact Containment.edge_containment common initial hb a b ha hab
  exact edgeFacts_of_containment_of_not_two common hcontain (fun a b ha hab =>
    OrderTwo.edge_commutator_card_ne_two common hb initial hcontain a b ha hab)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early
