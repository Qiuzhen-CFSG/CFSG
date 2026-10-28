module
public import Stellmacher.SectionNine.NineFourIntersectionIndex
public import Stellmacher.SectionFiveToSeven.ResidualTransport

/-!
# Normalizing and enlarging a counterexample to (9.4)

The record in this module stores exactly the original ambient (9.4)
parameters and hypotheses together with the negated conclusion. Every such
counterexample at critical distance greater than one yields another one
whose moved remote vertex neighbors the initial vertex and whose subgroup
contains the intersection of the moved-remote and next modules. The new
counterexample also carries the proved index-at-least-four inequality.

Choose a common neighbor on the distance-two path and a next-stabilizer
actor moving it to the initial vertex. Conjugate the remote vertex, actor,
residual commutator element, and subgroup by the same automorphism. Graph
covariance preserves the path distance; subgroup covariance preserves the
centralizer and commutator hypotheses, the edge-generation equality, and
the exact displacement cardinality. The enlargement lemma then adjoins
the module intersection without changing noncontainment or the actor
commutator bound. Applying the intersection-index theorem gives the bound
needed in the subsequent two auxiliary cases.

This is the opening reduction of Stellmacher (9.4), printed p.50 of
`refs/files/stellmacher-n-group.pdf`. It is an assembly interface and makes
no assertion that either remaining auxiliary case has been excluded.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public structure NineFourCounterexample
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B) where
  remote : ctx.Γ.Vertex
  distance : ctx.Γ.distance remote ctx.criticalPath.firstStep = 2
  actor : G
  actor_mem : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep
  actor_centralizes : actor ∈ Subgroup.centralizer (VAt ctx.Γ remote : Set G)
  conjugator : G
  conjugator_mem : conjugator ∈ ⁅EAt ctx.Γ ctx.criticalPath.firstStep, Subgroup.zpowers actor⁆
  subgroup : Subgroup G
  subgroup_le : subgroup ≤ VAt ctx.Γ (ctx.Γ.act conjugator remote)
  commutator_le : ⁅subgroup, Subgroup.zpowers actor⁆ ≤ VAt ctx.Γ ctx.criticalPath.firstStep
  generates : ∀ neighbor : ctx.Γ.Vertex,
    neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep →
    neighbor ∈ Neighborhood ctx.Γ (ctx.Γ.act conjugator remote) →
    (GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ neighbor) ⊔
      Subgroup.zpowers actor = GAt ctx.Γ ctx.criticalPath.firstStep
  displacement : QuotientCardEq
    (⁅VAt ctx.Γ ctx.criticalPath.firstStep, Subgroup.zpowers actor⁆ ⊔
      ZAt ctx.Γ ctx.criticalPath.firstStep)
    (ZAt ctx.Γ ctx.criticalPath.firstStep) 2
  not_le : ¬ subgroup ≤ VAt ctx.Γ ctx.criticalPath.firstStep

private theorem residual_stabilizer_transport
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (mover : G) (vertex : Γ.Vertex) :
    EAt Γ (Γ.act mover vertex) =
      (EAt Γ vertex).map (MulAut.conj mover⁻¹).toMonoidHom := by
  change Γ.twoResidualAt _ = (Γ.twoResidualAt _).map _
  rw [Γ.twoResidualAt_def, Γ.twoResidualAt_def]
  change twoResidualIn (stabilizer Γ (Γ.act mover vertex)) = _
  rw [stabilizer_act, conjugateBy, twoResidualIn_map_equiv]
  rfl

public theorem nine_four_normalized_enlarged_counterexample
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) (data : NineFourCounterexample ctx) :
    ∃ normalized : NineFourCounterexample ctx,
      ctx.Γ.act normalized.conjugator normalized.remote ∈
        Neighborhood ctx.Γ ctx.criticalPath.a ∧
      ctx.Γ.act normalized.conjugator normalized.remote ≠ ctx.criticalPath.firstStep ∧
      VAt ctx.Γ (ctx.Γ.act normalized.conjugator normalized.remote) ⊓
        VAt ctx.Γ ctx.criticalPath.firstStep ≤ normalized.subgroup ∧
      4 * Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
        VAt ctx.Γ (ctx.Γ.act normalized.conjugator normalized.remote) : Subgroup G) ≤
          Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let oldMoved := Γ.act data.conjugator data.remote
  have hdistance : Γ.distance oldMoved cp.firstStep = 2 :=
    nine_four_moved_distance Γ cp.firstStep data.remote data.actor data.conjugator
      data.actor_mem data.conjugator_mem data.distance
  have hnormalize := nine_four_normalize_two_path ctx.toLocalContext oldMoved hdistance
  dsimp only [AmbientSectionNineContext.toLocalContext] at hnormalize
  obtain ⟨neighbor, mover, hneighbor, hremote, hmover, hmove, hfix, hnew, hne⟩ := hnormalize
  let equiv := MulAut.conj mover⁻¹
  let f := equiv.toMonoidHom
  let newRemote := Γ.act mover data.remote
  let newActor := f data.actor
  let newConjugator := f data.conjugator
  let newSubgroup := data.subgroup.map f
  have hP : (GAt Γ cp.firstStep).map f = GAt Γ cp.firstStep := by
    change (stabilizer Γ cp.firstStep).map _ = _
    rw [← conjugateBy, ← stabilizer_act, hfix]
  have hU : (VAt Γ cp.firstStep).map f = VAt Γ cp.firstStep := by
    change (v Γ cp.firstStep).map _ = _
    rw [← v_act, hfix]
  have hZ : (ZAt Γ cp.firstStep).map f = ZAt Γ cp.firstStep := by
    change (z Γ cp.firstStep).map _ = _
    rw [← z_act, hfix]
  have hE : (EAt Γ cp.firstStep).map f = EAt Γ cp.firstStep := by
    rw [← residual_stabilizer_transport, hfix]
  have hmoved : Γ.act newConjugator newRemote = Γ.act mover oldMoved := by
    dsimp [newConjugator, newRemote, oldMoved, f, equiv]
    rw [inv_inv]
    rw [← Γ.act_mul, ← Γ.act_mul]
    congr 1
    group
  have hactor : newActor ∈ GAt Γ cp.firstStep := by
    rw [← hP]
    exact Subgroup.mem_map_of_mem f data.actor_mem
  have hcentral : newActor ∈ Subgroup.centralizer (VAt Γ newRemote : Set G) := by
    have hm := Subgroup.map_centralizer_le_centralizer_image
      (VAt Γ data.remote : Set G) f (Subgroup.mem_map_of_mem f data.actor_centralizes)
    change newActor ∈ Subgroup.centralizer ((VAt Γ data.remote).map f : Set G) at hm
    change newActor ∈ Subgroup.centralizer (v Γ newRemote : Set G)
    rw [v_act]
    exact hm
  have hconjugator : newConjugator ∈
      ⁅EAt Γ cp.firstStep, Subgroup.zpowers newActor⁆ := by
    have hm := Subgroup.mem_map_of_mem f data.conjugator_mem
    rw [Subgroup.map_commutator, hE, MonoidHom.map_zpowers] at hm
    exact hm
  have hsubgroup : newSubgroup ≤ VAt Γ (Γ.act newConjugator newRemote) := by
    rw [hmoved]
    change data.subgroup.map f ≤ v Γ (Γ.act mover oldMoved)
    rw [v_act]
    exact Subgroup.map_mono data.subgroup_le
  have hcomm : ⁅newSubgroup, Subgroup.zpowers newActor⁆ ≤ VAt Γ cp.firstStep := by
    have hm := Subgroup.map_mono (f := f) data.commutator_le
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers, hU] at hm
    exact hm
  have hgen : ∀ neighbor : Γ.Vertex,
      neighbor ∈ Neighborhood Γ cp.firstStep →
      neighbor ∈ Neighborhood Γ (Γ.act newConjugator newRemote) →
      (GAt Γ cp.firstStep ⊓ GAt Γ neighbor) ⊔
        Subgroup.zpowers newActor = GAt Γ cp.firstStep := by
    intro next hnext hnewNext
    let before := Γ.act mover⁻¹ next
    have hinv : Γ.act mover⁻¹ cp.firstStep = cp.firstStep :=
      (Set.ext_iff.mp (Γ.stabilizer_def cp.firstStep) mover⁻¹).mp
        ((GAt Γ cp.firstStep).inv_mem hmover)
    have hbefore : before ∈ Neighborhood Γ cp.firstStep := by
      apply (mem_neighborhood_iff_adjacent Γ).mpr
      have hh := adjacent_act Γ mover⁻¹ ((mem_neighborhood_iff_adjacent Γ).mp hnext)
      rwa [hinv] at hh
    have hbeforeRemote : before ∈ Neighborhood Γ oldMoved := by
      apply (mem_neighborhood_iff_adjacent Γ).mpr
      have hh := adjacent_act Γ mover⁻¹ ((mem_neighborhood_iff_adjacent Γ).mp hnewNext)
      rw [hmoved, ← Γ.act_mul, mul_inv_cancel, Γ.act_one] at hh
      exact hh
    have hback : Γ.act mover before = next := by
      dsimp [before]
      rw [← Γ.act_mul, inv_mul_cancel, Γ.act_one]
    have hN : (GAt Γ before).map f = GAt Γ next := by
      change (stabilizer Γ before).map _ = _
      rw [← conjugateBy, ← stabilizer_act, hback]
    have hh := congrArg (fun K : Subgroup G => K.map f)
      (data.generates before hbefore hbeforeRemote)
    rw [Subgroup.map_sup, Subgroup.map_inf _ _ f equiv.injective,
      hP, hN, MonoidHom.map_zpowers] at hh
    exact hh
  have hdisp : QuotientCardEq
      (⁅VAt Γ cp.firstStep, Subgroup.zpowers newActor⁆ ⊔ ZAt Γ cp.firstStep)
      (ZAt Γ cp.firstStep) 2 := by
    have hm := data.displacement
    unfold QuotientCardEq at hm ⊢
    have hc := Subgroup.card_map_of_injective (f := f) (K :=
      ⁅VAt Γ cp.firstStep, Subgroup.zpowers data.actor⁆ ⊔ ZAt Γ cp.firstStep) equiv.injective
    rw [Subgroup.map_sup, Subgroup.map_commutator, hU, hZ, MonoidHom.map_zpowers] at hc
    exact hc.trans hm
  have hnot : ¬ newSubgroup ≤ VAt Γ cp.firstStep := by
    intro hle
    apply data.not_le
    exact (Subgroup.map_le_map_iff_of_injective equiv.injective).mp (hU.symm ▸ hle)
  have hnewDistance : Γ.distance newRemote cp.firstStep = 2 := by
    rw [← hfix, distance_act]
    exact data.distance
  have hmovedDistance : Γ.distance (Γ.act newConjugator newRemote) cp.firstStep = 2 :=
    nine_four_moved_distance Γ cp.firstStep newRemote newActor newConjugator
      hactor hconjugator hnewDistance
  have henlarged := nine_four_enlargement ctx.toLocalContext hb
    (Γ.act newConjugator newRemote) hmovedDistance newActor hactor newSubgroup hsubgroup hcomm
  dsimp only [AmbientSectionNineContext.toLocalContext] at henlarged
  let enlarged := newSubgroup ⊔ (VAt Γ (Γ.act newConjugator newRemote) ⊓ VAt Γ cp.firstStep)
  let normalized : NineFourCounterexample ctx := {
    remote := newRemote
    distance := hnewDistance
    actor := newActor
    actor_mem := hactor
    actor_centralizes := hcentral
    conjugator := newConjugator
    conjugator_mem := hconjugator
    subgroup := enlarged
    subgroup_le := henlarged.2.1
    commutator_le := henlarged.2.2.2.1
    generates := hgen
    displacement := hdisp
    not_le := fun hle => hnot (henlarged.1.trans hle) }
  refine ⟨normalized, ?_, ?_, henlarged.2.2.1, ?_⟩
  · change Γ.act newConjugator newRemote ∈ Neighborhood Γ cp.a
    rw [hmoved]
    exact hnew
  · change Γ.act newConjugator newRemote ≠ cp.firstStep
    rw [hmoved]
    exact hne
  · exact nine_four_counterexample_intersection_index ctx hb normalized.remote normalized.distance
      normalized.actor ⟨normalized.actor_mem, normalized.actor_centralizes⟩
      normalized.conjugator normalized.conjugator_mem normalized.subgroup
      normalized.subgroup_le normalized.commutator_le normalized.generates
      normalized.displacement normalized.not_le

end Stellmacher.SectionNine
