module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Centrality.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Center
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Obstruction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.LocalStructure


/-!
# Applying the radius obstruction to the centrality pair

For the noncentral generator pair in (4.6.3), critical reversal supplies an
edge at delta whose kernel contains the actual actor Z_lambda. This actor
is elementary abelian and finite, so its intrinsic Frattini subgroup is
trivial. The proved center containment discharges the remaining premise of
(4.6.2). Thus a small-displacement estimate on V_delta/Z_delta implies
V_delta' <= U_delta, using exactly the published quotient-centralizer preimage.

The transported marked natural action makes every nonzero invariant subgroup
of U_delta equal to U_delta. The radius-derived subgroup is invariant and
nontrivial, so the containment upgrades to equality, which transports to all
M-vertices. Only the displacement estimate remains explicit here; it is not
replaced by a classification assumption.

Source: Meierfrankenfeld--Stellmacher (1993), first paragraph of (4.6.3),
printed pp.901--902, using (4.6.1)--(4.6.2).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
private theorem natural_irreducible
    (common : CommonFacts R source geometry) (a : Vertex R) (ha : color R a = false)
    (K : Subgroup (FreeAmalgam R)) (hK : K ≤ U R a)
    (hn : stabilizer R a ≤ normalizer (K : Set (FreeAmalgam R))) :
    K = ⊥ ∨ K = U R a := by
  obtain ⟨frame⟩ := ModuleAlternatives.SourceCalculation.exists_frame a ha
  let model := frame.natural common.natural
  let S := stabilizer R a
  have hUS : U R a ≤ S := (U_le_Z a).trans (Z_le_stabilizer R a)
  let e := (subgroupOfEquivOfLe hUS).trans model.equiv
  let n : RankOnePairing.NaturalFactor (frame.projection source) ⊤ ((U R a).subgroupOf S) ⊥ := {
    marking := model.marking
    coordinates := e.toMonoidHom
    surjective := e.surjective
    kernel := by rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective, bot_subgroupOf]
    normalized := by
      intro g _
      rw [← subgroupOf_normalizer_eq hUS]
      exact U_normalized a g.property
    action := by
      intro g _ x y h
      exact model.action g ((subgroupOfEquivOfLe hUS) x)
        ((subgroupOfEquivOfLe hUS) y) (congrArg Subtype.val h) }
  have hm : (⊤ : Subgroup S).map (frame.projection source) = ⊤ :=
    map_top_of_surjective _ (frame.projection_surjective source)
  have hnorm : (⊤ : Subgroup S) ≤ normalizer (K.subgroupOf S : Set S) := by
    intro g _
    rw [← subgroupOf_normalizer_eq (hK.trans hUS)]
    exact hn g.property
  rcases n.irreducible hm (K.subgroupOf S) (subgroupOf_mono S hK) hnorm with h | h
  · left
    have hh := congrArg (Subgroup.map S.subtype) h
    simpa only [map_subgroupOf_eq_of_le (hK.trans hUS), Subgroup.map_bot] using hh
  · right
    have hh := congrArg (Subgroup.map S.subtype) h
    simpa only [map_subgroupOf_eq_of_le (hK.trans hUS), map_subgroupOf_eq_of_le hUS] using hh

/-- The nonzero radius-derived subgroup fills U whenever it is contained in U. -/
theorem radius_derived_eq_U_of_le
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a : Vertex R) (ha : color R a = false) (hle : ⁅V R a,V R a⁆ ≤ U R a) :
    ⁅V R a,V R a⁆ = U R a := by
  have hn : stabilizer R a ≤ normalizer (⁅V R a,V R a⁆ : Subgroup (FreeAmalgam R)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (V_normalized a hg)]
  exact (natural_irreducible common a ha _ hle hn).resolve_left
    (radius_derived_ne_bot common hb a ha)

omit [Finite M] in
/-- The derived equality transports by the actual free-amalgam conjugations. -/
theorem radius_derived_eq_U_at_all
    (a c : Vertex R) (ha : color R a = false) (hc : color R c = false)
    (heq : ⁅V R a,V R a⁆ = U R a) : ⁅V R c,V R c⁆ = U R c := by
  obtain ⟨u,hu⟩ := exists_mVertex_of_color R ha
  obtain ⟨v,hv⟩ := exists_mVertex_of_color R hc
  let g := u⁻¹ * v
  have hg : act R g a = c := by
    rw [hu,act_mVertex]
    simpa only [g,mul_inv_cancel_left] using hv.symm
  rw [← hg,V_act,U_act,← map_commutator,heq]

namespace NoncentralPair
variable {a d e : Vertex R}

/-- Apply (4.6.2) to Z_lambda, discharging the edge, Frattini and center premises. -/
theorem derived_le_U_of_small_displacement (h : NoncentralPair R a d e)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (hsmall : (radiusFixed geometry d (Z R e)).relIndex (V R d) ≤
      (Q R d).relIndex (Z R e)) : ⁅V R d,V R d⁆ ≤ U R d := by
  have hcrit := h.critical_pair common hb
  have hrev := common.critical_reverse d h.color_d e h.color_e hcrit
  obtain ⟨t,hdt,_,hEt⟩ := critical_predecessor R e h.color_e _
    (by rw [geometry.distance_constant e h.color_e]; change 0 < geometry.b R; omega) hrev
  let := finite_stabilizer R e
  let : Finite (Z R e) := Finite.of_injective
    (inclusion (Z_le_stabilizer R e)) (inclusion_injective _)
  let := geometry.Z_elementary (by omega) e h.color_e
  let : Fact (IsPGroup 2 (Z R e)) :=
    ⟨(Q_isPGroup R source.two_group source.core_le e h.color_e).to_le
      (by rw [← common.X_eq_Z e h.color_e]; exact omegaCenter_le _)⟩
  apply radius_offender_obstruction common hb (radius_center_le_B source geometry common hb)
    d t h.color_d hdt (Z R e) hEt hrev.2 _ hsmall
  rw [frattini_eq_bot_of_isElementaryAbelian (p := 2),Subgroup.map_bot]
  exact bot_le

/-- The first source consequence of small displacement in (4.6.3). -/
theorem derived_eq_U_of_small_displacement (h : NoncentralPair R a d e)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (hsmall : (radiusFixed geometry d (Z R e)).relIndex (V R d) ≤
      (Q R d).relIndex (Z R e)) : ⁅V R d,V R d⁆ = U R d :=
  radius_derived_eq_U_of_le common hb d h.color_d
    (h.derived_le_U_of_small_displacement common hb hsmall)
end NoncentralPair
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
