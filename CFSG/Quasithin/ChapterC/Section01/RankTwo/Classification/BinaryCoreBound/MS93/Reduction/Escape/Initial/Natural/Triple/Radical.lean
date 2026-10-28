module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Triple.Radical.Head
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Triple.Radical.Linear

/-!
# The moving part of the two-core-fixed dual space

If the residual fixed the two-core-fixed space of the dual of V_a/Z_a,
annihilator duality would make it fix V_a/(Z_a[V_a,Q_a]). The radius-head
nontriviality theorem excludes this using the actual local geometry.
All normalities and quotient actions are inside the finite vertex stabilizer;
the contradiction is transported through its inclusion into the free amalgam.

Source: Meierfrankenfeld--Stellmacher (1993), the dual-module step of
(4.3.1)(iii), p.883, with the expanded notation c(U) on p.881.
-/

public section

open Subgroup Representation Stellmacher.PushingUp.AmalgamGraph
open Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Triple
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The residual moves the two-core-fixed space of the actual dual radius module. -/
theorem radius_dual_fixedSpace_moving (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false) :
    let S := stabilizer R a
    let H := (V R a).subgroupOf S
    let N := (Z R a).subgroupOf S
    letI := radius_normal a
    letI := geometry.Z_normal a
    letI : IsElementaryAbelian 2 (H ⧸ N.subgroupOf H) :=
      elementary_radius_quotient source geometry hb modules a ha
    ¬ fixedSpace (sectionRepresentation H N).dual ((Q R a).subgroupOf S) ≤
      fixedSpace (sectionRepresentation H N).dual (pResidual 2 S) := by
  let S := stabilizer R a
  let H := (V R a).subgroupOf S
  let N := (Z R a).subgroupOf S
  let := radius_normal (R := R) a
  let := geometry.Z_normal a
  let : IsElementaryAbelian 2 (H ⧸ N.subgroupOf H) :=
    elementary_radius_quotient source geometry hb modules a ha
  change ¬ fixedSpace (sectionRepresentation H N).dual ((Q R a).subgroupOf S) ≤
    fixedSpace (sectionRepresentation H N).dual (pResidual 2 S)
  intro h
  have hh := commutator_le_sup_of_dual_fixedSpace_le H N
    ((Q R a).subgroupOf S) (pResidual 2 S) h
  have hm := map_mono (f := S.subtype) hh
  rw [Subgroup.map_sup, map_commutator, map_commutator,
    map_subgroupOf_eq_of_le ((geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)),
    map_subgroupOf_eq_of_le (show Q R a ≤ S from fun _ hx => hx.1),
    map_subgroupOf_eq_of_le (Z_le_stabilizer R a)] at hm
  exact radius_head_moving source geometry hb modules a ha hm

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Triple
