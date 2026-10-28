module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Triple.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Elementary

/-!
# The source input to the dual radius-module argument

The actual local V_a/Z_a is elementary abelian. The already proved radius
image bound therefore makes the fixed-space codimension of the endpoint
actor at most one on its dual. Critical-index reciprocity also identifies
the endpoint actor's image in the specified SL3(2) quotient as a group of
order two. Its original subgroup is elementary abelian and the projection
has a two-group kernel.

These are inputs to representation recognition. The final transport lemma
keeps the needed dual fixedness explicit; neither that premise nor the
unconditional triple bound is asserted here. All quotients and normalities
are relative to the finite stabilizer. The final conclusion is transported
back to the actual free amalgam.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.1)(ii)--(iii), pp.882--883,
and the definition of c(U), p.881.
-/

public section

open Subgroup Representation Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Triple

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The literal dual radius quotient has endpoint fixed codimension at most one. -/
theorem radius_dual_displacement (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry) :
    let S := stabilizer R p.a
    let H := (V R p.a).subgroupOf S
    let N := (Z R p.a).subgroupOf S
    let := radius_normal p.a
    let := geometry.Z_normal p.a
    letI : IsElementaryAbelian 2 (H ⧸ N.subgroupOf H) :=
      elementary_radius_quotient source geometry hb modules p.a p.color_a
    Representation.BinaryOffender.fixedCodim (sectionRepresentation H N).dual
      ((Z R p.a').subgroupOf S) ≤ 1 := by
  let S := stabilizer R p.a
  let H := (V R p.a).subgroupOf S
  let N := (Z R p.a).subgroupOf S
  let A := (Z R p.a').subgroupOf S
  let := radius_normal (R := R) p.a
  let := geometry.Z_normal p.a
  let : IsElementaryAbelian 2 (H ⧸ N.subgroupOf H) :=
    elementary_radius_quotient source geometry hb modules p.a p.color_a
  let := finite_stabilizer R p.a
  apply dual_fixedCodim_le_one H N A
  have hVS : V R p.a ≤ S := (geometry.V_le_Q hb p.a p.color_a).trans (fun _ hx => hx.1)
  have hZS : Z R p.a ≤ S := Z_le_stabilizer R p.a
  have hAS : Z R p.a' ≤ S := p.end_Z_le_start_stabilizer
  have hindex : N.relIndex ⁅H, A⁆ = (Z R p.a).relIndex (radiusCommutator p.a p.a') := by
    rw [← relIndex_map_map_of_injective N ⁅H, A⁆ S.subtype_injective,
      map_commutator, map_subgroupOf_eq_of_le hZS,
      map_subgroupOf_eq_of_le hVS, map_subgroupOf_eq_of_le hAS]
    rfl
  rw [hindex]
  exact radius_quotient_image_le_two p source hb modules

/-- Critical reciprocity identifies the endpoint actor in the local quotient. -/
theorem endpoint_quotient_image_card (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry)
    (hfour : Nat.card (radiusCommutator p.a p.a') = 4)
    (π : stabilizer R p.a →* SL)
    (hπ : π.ker = (Q R p.a).subgroupOf (stabilizer R p.a)) :
    Nat.card (((Z R p.a').subgroupOf (stabilizer R p.a)).map π) = 2 := by
  let s : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  have hrev := source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical
  rw [← relIndex_ker, hπ, relIndex_subgroupOf p.end_Z_le_start_stabilizer,
    s.critical_Z_index_eq_U geometry p.a' p.end_color p.a hrev,
    modules.critical_U_index p.a' p.end_color p.a hrev,
    ← s.critical_Z_index_eq_U geometry p.a p.color_a p.a' p.critical]
  exact critical_index_of_radius_card_four p source hb modules hfour

/-- The final group-theoretic transport, with dual fixedness still explicit. -/
theorem radius_triple_of_dual_fixed (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false)
    (hd : let S := stabilizer R a
      let H := (V R a).subgroupOf S
      let N := (Z R a).subgroupOf S
      letI := radius_normal a
      letI := geometry.Z_normal a
      letI : IsElementaryAbelian 2 (H ⧸ N.subgroupOf H) :=
        elementary_radius_quotient source geometry hb modules a ha
      Coinvariants.ker ((sectionRepresentation H N).dual.comp (pResidual 2 S).subtype) ≤
        invariants ((sectionRepresentation H N).dual.comp ((Q R a).subgroupOf S).subtype)) :
    ⁅⁅V R a, Q R a⁆, Ltilde R a⁆ ≤ Z R a := by
  let S := stabilizer R a
  let H := (V R a).subgroupOf S
  let N := (Z R a).subgroupOf S
  let := radius_normal (R := R) a
  let := geometry.Z_normal a
  let : IsElementaryAbelian 2 (H ⧸ N.subgroupOf H) :=
    elementary_radius_quotient source geometry hb modules a ha
  have hh := triple_le_of_dual_fixed H N ((Q R a).subgroupOf S) (pResidual 2 S) hd
  have hm := map_mono (f := S.subtype) hh
  rw [map_commutator, map_commutator,
    map_subgroupOf_eq_of_le ((geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)),
    map_subgroupOf_eq_of_le (show Q R a ≤ S from fun _ hx => hx.1),
    map_subgroupOf_eq_of_le (Z_le_stabilizer R a)] at hm
  exact hm

/-- The endpoint actor is elementary; its specified local quotient image has order two. -/
theorem exists_endpoint_projection (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry)
    (hfour : Nat.card (radiusCommutator p.a p.a') = 4) :
    ∃ π : stabilizer R p.a →* SL,
      Function.Surjective π ∧
      π.ker = (Q R p.a).subgroupOf (stabilizer R p.a) ∧
      IsPGroup 2 π.ker ∧
      IsElementaryAbelian 2 ((Z R p.a').subgroupOf (stabilizer R p.a)) ∧
      Nat.card (((Z R p.a').subgroupOf (stabilizer R p.a)).map π) = 2 := by
  obtain ⟨π, hsurj, hker⟩ := exists_localProjection source p.a p.color_a
  refine ⟨π, hsurj, hker, ?_, ?_, endpoint_quotient_image_card source geometry hb modules p hfour π hker⟩
  · rw [hker]
    exact (Q_isPGroup R source.two_group source.core_le p.a p.color_a).comap_subtype
  · let := geometry.Z_elementary (by omega) p.a' p.end_color
    exact IsElementaryAbelian.subgroupOf p.end_Z_le_start_stabilizer

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Triple
