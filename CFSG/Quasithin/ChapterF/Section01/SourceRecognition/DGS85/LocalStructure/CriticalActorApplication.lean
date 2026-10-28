module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.CriticalActorSelection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.FullGraphObstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.SourceConclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.BOneProfileSource

/-!
# Original noncommuting critical-center consumers

At every noncommuting critical pair the two proved actor markings supply
the existing natural-section recognition, both full-stabilizer Sylow products
and equal reciprocal core indices. When the pair meets both vertex orbits,
critical quotient selection and original conjugation give actual linear
actor quotients everywhere. Together with the unconditional 6.5 obstruction
this discharges the existing Chapter 7 consumer, including its two natural
center markings, equal field orders and both Sylow products.

At b=1 the critical pair is adjacent, so this also supplies the full
original parabolic natural-core coordinates with no enlarged-model or
order-144 premise. The distance bound for pairs within one orbit and the unrestricted 6.1
enlargement are still open. The source b, full Borel, original cores and
all maps in the existing consumers are preserved.
Source: DGS, *Groups and Graphs* (1985), 6.1, 6.5 and 7.1--7.5,
pp.118--119,121--122,126--131, and the original b=1 application in 10.1.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S

/-- If the noncommuting critical pair meets both vertex orbits, conjugation
supplies actual linear quotient markings at every vertex. -/
theorem reduced_cross_orbit_actor_models (h : HypothesisF11 L S)
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (htype : v.type ≠ w.type) (x : Vertex F) :
    ∃ n, 0 < n ∧ ClassicalGroup.IsPSL
      (graphLocalGroup F x ⧸ pCore 2 (graphLocalGroup F x)) 2 (2^n) := by
  have hm := reduced_critical_actor_quotients_linear h hc hne
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
  by_cases hx : v.type = x.type
  · exact transport v hx hm.1
  · have hw : w.type = x.type := by
      cases hv : v.type <;> cases hw : w.type <;> cases hx' : x.type <;> simp_all
    exact transport w hw hm.2

/-- The genuine Chapter 7 consumer on both vertex orbits now has all its
setup premises discharged, including the possible order-144 branch. -/
theorem reduced_cross_orbit_noncommuting_conclusion (h : HypothesisF11 L S)
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (htype : v.type ≠ w.type) :
    (b F = 1 ∨ b F = 2) ∧
    Noncommuting.EqualFieldNaturalCenters (graphLocalGroup F v) (Z F v) (Q F v)
      (graphLocalGroup F w) (Z F w) (Q F w) ∧
    Stellmacher.IsSylowSubgroupIn (Z F w ⊔ Q F v) (stabilizer F v) ∧
    Stellmacher.IsSylowSubgroupIn (Z F v ⊔ Q F w) (stabilizer F w) := by
  apply Noncommuting.Reduction.reduced_noncommuting_source_conclusion h ?_
    (fun x y he => reduced_graph_core_obstruction h y x he.symm) hc hne
  intro x
  obtain ⟨n,hn,hm⟩ := reduced_cross_orbit_actor_models h hc hne htype x
  exact .linear n hn hm

open NoncommutingProfile in
/-- At b=1 the original full-parabolic natural-core application has no
remaining actor-model or order-144 assumption. All coordinates are retained. -/
theorem original_bOne_natural_cores (h : HypothesisF11 L S)
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥)
    (hb : b F = 1) :
    IsElementaryAbelian 2 ((parabolic L S 0).pCoreIn 2) ∧
    IsElementaryAbelian 2 ((parabolic L S 1).pCoreIn 2) ∧
    ∃ (k₀ : Type u) (_ : Field k₀) (_ : Finite k₀) (_ : CharP k₀ 2) (_ : Algebra (ZMod 2) k₀)
      (k₁ : Type u) (_ : Field k₁) (_ : Finite k₁) (_ : CharP k₁ 2) (_ : Algebra (ZMod 2) k₁),
      ∃ (c₀ : BOneActionData F (base F false) (base F true) k₀ (Fin 2 → k₀))
        (c₁ : BOneActionData F (base F true) (base F false) k₁ (Fin 2 → k₁)),
        c₀.actor = graphLocalGroup F (base F false) ∧
        c₁.actor = graphLocalGroup F (base F true) ∧ Nat.card k₀ = Nat.card k₁ ∧
        OriginalNaturalCoreCoordinates false c₀ ∧ OriginalNaturalCoreCoordinates true c₁ := by
  have he : (graph F).Adj v w := SimpleGraph.dist_eq_one_iff_adj.mp (hc.1.trans hb)
  apply Noncommuting.Reduction.original_bOne_natural_cores_of_actor_models h ?_ hc hne hb
  intro x
  obtain ⟨n,hn,hm⟩ := reduced_cross_orbit_actor_models h hc hne he.1 x
  exact .linear n hn hm

/-- The source natural sections, both full-stabilizer Sylow products and
reciprocal core indices hold at every noncommuting critical pair. -/
theorem reduced_critical_natural_centers_and_products (h : HypothesisF11 L S)
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) :
    Noncommuting.HasNaturalCenter (graphLocalGroup F v) (Z F v) (Q F v) ∧
    Noncommuting.HasNaturalCenter (graphLocalGroup F w) (Z F w) (Q F w) ∧
    Stellmacher.IsSylowSubgroupIn (Z F w ⊔ Q F v) (stabilizer F v) ∧
    Stellmacher.IsSylowSubgroupIn (Z F v ⊔ Q F w) (stabilizer F w) ∧
    (Q F v).relIndex (Z F w) = (Q F w).relIndex (Z F v) := by
  let ht := reduced_triple h
  have hvw : v ≠ w := by
    intro he
    have hd := hc.1
    have hp : 0 < b F := source_b_positive ht
    rw [he,SimpleGraph.dist_self] at hd
    omega
  obtain ⟨a,hva,_⟩ := exists_predecessor F ht.generate w v hvw.symm
  obtain ⟨t,hwt,_⟩ := exists_predecessor F ht.generate v w hvw
  have hc' := (reduced_noncommuting_critical_intersections h hc hne).1
  obtain ⟨c₀,he₀⟩ := reduced_critical_actor_localData h hc hne hva
  obtain ⟨c₁,he₁⟩ := reduced_critical_actor_localData h hc' (by rwa [commutator_comm]) hwt
  have ho₀ : ¬ 2 ∣ c₀.Pstar.relIndex (stabilizer F v) := by
    rw [he₀]
    exact Noncommuting.graph_actor_odd_index ht v
  have ho₁ : ¬ 2 ∣ c₁.Pstar.relIndex (stabilizer F w) := by
    rw [he₁]
    exact Noncommuting.graph_actor_odd_index ht w
  have hn := Noncommuting.Reduction.reduced_critical_natural_centers_and_products h
    hc hne _ _ c₀ c₁ ho₀ ho₁
  have hi := Noncommuting.Reduction.reduced_critical_core_indices_eq_of_localData h
    hc hne _ _ c₀ c₁ ho₀ ho₁
  rw [he₀,he₁] at hn
  exact ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2,hi⟩


end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
