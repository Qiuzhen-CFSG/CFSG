module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Noncentral.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Center.Reduction

/-!
# Assembly of the early distance-four source clauses

The initial factorization and edge calculations are proved from the common
source data. Two subsequent source steps remain explicit: the transfer from
centrality of V_a' to component fixation of [Vcirc_a,Q_a], and placement of B_d
in an incident edge radius at the selected noncentral generator. The imported
reductions make the selection and turn these steps into derived noncentrality
and the center equality.

This conditional constructor does not discharge the two remaining steps or
complete EarlyFacts from CommonFacts alone. Their construction and the final
application belong to this early distance-four argument.

Source: Meierfrankenfeld--Stellmacher (1993), both assertions labeled (4.6.6)
and (4.6.7), printed pp.903--904.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
open Early
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Assemble the early facts after the two local source steps on pp.903--904.
InitialFacts and EdgeFacts are constructed here, rather than assumed. -/
theorem earlyFacts_of_local_steps
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (transfer : InitialFacts R geometry → EdgeFacts R →
      ∀ a, color R a = false →
        ⁅V R a, V R a⁆ ≤ (center (stabilizer R a)).map (stabilizer R a).subtype →
        ⁅Vcirc R a, Q R a⁆ ≤ fixedCore R a)
    (placement : InitialFacts R geometry → EdgeFacts R →
      (∀ a, color R a = false →
        ¬ ⁅V R a, V R a⁆ ≤ (center (stabilizer R a)).map (stabilizer R a).subtype) →
      ∀ a b d, color R a = false → Adjacent R a b → Adjacent R d b →
        (¬ B R a (geometry.Z_normal a) ≤ (center (V R a)).map (V R a).subtype) →
        ⁅B R a (geometry.Z_normal a), Z R d⁆ ≠ ⊥ →
        B R d (geometry.Z_normal d) ≤ V R b) :
    EarlyFacts R geometry := by
  have initial := initialFacts source geometry common hb
  have edge := edgeFacts_of_initial common hb initial
  have hnoncentral := derived_noncentral_of_kernel_transfer common hb
    (fun a ha hcentral => kernel_central_of_moving_fixed common edge a ha
      (transfer initial edge a ha hcentral))
  exact {
    commutator_central := initial.commutator_central
    commutator_le_Z := edge.commutator_le_Z
    edge_commutator_card := edge.edge_commutator_card
    edge_Z_index := edge.edge_Z_index
    edge_Q_index := edge.edge_Q_index
    derived_noncentral := hnoncentral
    B_eq_center := B_eq_center_of_failure_edge_placement common initial (by
      intro a b ha hab hfail
      obtain ⟨d, hdb, hseed⟩ :=
        exists_noncentral_edge_generator_of_center_failure common a b ha hab hfail
      exact ⟨d, hdb, placement initial edge hnoncentral a b d ha hab hdb hfail hseed⟩) }

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
