module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallProjectiveGraphCatalogue
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicNoncommutingBound
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.CriticalProfileCentral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoDihedralExclusion
public import Theory.SpecificGroups.GL2.ThreeSylowNormalElementary

/-!
# Both actor orbits on the original noncommuting branch

At distance two, the intrinsic critical action and middle-center identities
give the source seed obstruction at any middle vertex. If its quotient were
the order-144 enlargement, its normal nine-group would put every normal
elementary Sylow subgroup in Frattini, contradicting that seed obstruction.
The existing catalogue selection then makes the middle quotient linear.
This argument retains arbitrary vertices and both endpoint orientations.

The unconditional distance bound reduces every noncommuting critical pair
to distances one or two. Critical and middle markings therefore cover both
orbits and supply the actual Chapter 7 consumer without a global model
premise. The unrestricted enlargement in commuting branches remains open.
Source: DGS, Groups and Graphs (1985), Theorem B(a), p.102; (7.1)--(7.5),
pp.126--131; (10.7)--(10.9), pp.158--163.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.AmalgamGraph
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open Noncommuting NoncommutingProfile
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (G₀ L S))

/-- The middle actor is linear for every original distance-two noncommuting
critical pair, in either vertex orientation. -/
theorem reduced_bTwo_middle_quotient_linear (h : HypothesisF11 L S)
    {v m w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : b F = 2) (hvm : (graph F).Adj v m) (hmw : (graph F).Adj m w) :
    ∃ n, 0 < n ∧ ClassicalGroup.IsPSL
      (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) 2 (2^n) := by
  obtain ⟨k,hk,hfin,hchar,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hvm hmw
  have ha : alg = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  obtain ⟨d,_⟩ := reduced_critical_actor_localData h hc hne hvm
  obtain ⟨g,hg,hng⟩ := SetLike.exists_of_lt (source_borel_lt d)
  have hfix : g • v = v := hg
  have ht : (graph F).Adj v (g • m) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hvm
    change (graph F).Adj (g • v) (g • m) at hh
    simpa only [hfix] using hh
  have htne : g • m ≠ m := fun he => hng ⟨hg,he⟩
  have hcentral := reduced_bTwo_middle_central h hc hne hb hvm hmw
  have hcomm := (reduced_bTwo_center_identities h hc hne hb hvm hmw).2.2.2
  have hnot := reduced_graph_core_obstruction h v m hvm
  have hsplit := reduced_graph_rankOne_or_normal_nine h m
  dsimp only [reducedFamily] at hsplit
  rcases hsplit with hm | ⟨hcard,N,hN,hNelem,h9⟩
  · exact c.beta_quotient_linear (reduced_triple h) (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb hactor hcentral ht htne hcomm hnot
      (LinearEquiv.refl _ _) hm
  · let : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
    let M := graphLocalGroup F m
    let H := M ⧸ pCore 2 M
    let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
    let := hN
    let := hNelem
    exfalso
    apply c.not_beta_normal_elementary_le_frattini (reduced_triple h)
      (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hb hactor hcentral
      ht htne hcomm.le hnot (MulEquiv.refl H)
    intro T E hET hnE hE
    let := hE
    have hEnormal : (E.subgroupOf (T : Subgroup H)).Normal :=
      (normal_subgroupOf_iff_le_normalizer hET).mpr hnE
    have hEelem : IsElementaryAbelian 2 (E.subgroupOf (T : Subgroup H)) :=
      IsElementaryAbelian.comap_of_injective (T : Subgroup H).subtype
        (T : Subgroup H).subtype_injective E
    have hh := @normal_elementary_le_frattini_of_normal_nine H _ _ hcard N hN hNelem h9
      (pCore_quotient_pCore_eq_bot (G := M) 2) T (E.subgroupOf (T : Subgroup H)) hEnormal hEelem
    have hh' := map_mono (f := (T : Subgroup H).subtype) hh
    rwa [map_subgroupOf_eq_of_le hET] at hh'

/-- Every actor quotient is linear whenever the original graph has a
noncommuting critical pair; no basepoint or orientation is prescribed. -/
theorem reduced_noncommuting_actor_quotients_linear (h : HypothesisF11 L S)
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (x : Vertex F) :
    ∃ n, 0 < n ∧ ClassicalGroup.IsPSL
      (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)) 2 (2^n) := by
  rcases reduced_intrinsic_noncommuting_bound h hc hne with hb | hb
  · exact reduced_cross_orbit_actor_models h hc hne
      (SimpleGraph.dist_eq_one_iff_adj.mp (hc.1.trans hb)).1 x
  · have hvw : v ≠ w := by
      intro he
      have hh := hc.1
      rw [he,SimpleGraph.dist_self] at hh
      omega
    obtain ⟨m,hwm,hd⟩ := exists_predecessor F (reduced_triple h).generate v w hvw
    have hvm : (graph F).Adj v m := SimpleGraph.dist_eq_one_iff_adj.mp (by
      have hh := hc.1
      omega)
    obtain ⟨nm,hnm,hmm⟩ := reduced_bTwo_middle_quotient_linear h hc hne hb hvm hwm.symm
    obtain ⟨nv,hnv,hmv⟩ := (reduced_critical_actor_quotients_linear h hc hne).1
    have transport (a : Vertex F) (ha : a.type = x.type)
        (hm : ∃ n, 0 < n ∧ ClassicalGroup.IsPSL
          (graphLocalGroup F a ⧸ pCore 2 (graphLocalGroup F a)) 2 (2^n)) :
        ∃ n, 0 < n ∧ ClassicalGroup.IsPSL
          (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)) 2 (2^n) := by
      obtain ⟨g,hg⟩ := (same_orbit_iff F a x).mpr ha
      let A := graphLocalGroup F a
      have he : A.map (MulAut.conj g).toMonoidHom = graphLocalGroup F x :=
        (graphLocalGroup_conjugate (reduced_triple h) g a).symm.trans
          (congrArg (graphLocalGroup F) hg)
      let e : A ≃* graphLocalGroup F x :=
        (A.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
          (MulEquiv.subgroupCongr he)
      obtain ⟨n,hn,hmodel⟩ := hm
      exact ⟨n,hn,hmodel.of_mulEquiv (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm⟩
    by_cases hvx : v.type = x.type
    · exact transport v hvx ⟨nv,hnv,hmv⟩
    · have hmx : m.type = x.type := by
        have hvmtype := hvm.1
        cases hv : v.type <;> cases hm : m.type <;> cases hx : x.type <;> simp_all
      exact transport m hmx ⟨nm,hnm,hmm⟩

/-- The literal Chapter 7 conclusion with every earlier actor and core
obstruction premise discharged from the original noncommuting source. -/
theorem reduced_intrinsic_noncommuting_conclusion (h : HypothesisF11 L S)
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) :
    (b F = 1 ∨ b F = 2) ∧
    Noncommuting.EqualFieldNaturalCenters (graphLocalGroup F v) (Z F v) (Q F v)
      (graphLocalGroup F w) (Z F w) (Q F w) ∧
    Stellmacher.IsSylowSubgroupIn (Z F w ⊔ Q F v) (stabilizer F v) ∧
    Stellmacher.IsSylowSubgroupIn (Z F v ⊔ Q F w) (stabilizer F w) := by
  apply Noncommuting.Reduction.reduced_noncommuting_source_conclusion h ?_
    (fun x y he => reduced_graph_core_obstruction h y x he.symm) hc hne
  intro x
  obtain ⟨n,hn,hm⟩ := reduced_noncommuting_actor_quotients_linear h hc hne x
  exact .linear n hn hm

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
