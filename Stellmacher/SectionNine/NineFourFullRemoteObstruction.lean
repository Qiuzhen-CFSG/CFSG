module
public import Stellmacher.SectionNine.NineFourResidualSupplement
public import Stellmacher.SectionNine.NineFourNeighborJoin
public import Stellmacher.SectionNine.NineFourReduction

/-!
# The actor cannot compress the full remote module

At critical distance greater than one, an actor generating the next
stabilizer together with an edge through a common neighbor cannot have
the entire remote module's commutator contained in the next module.
The first theorem proves the normalized initial-edge case; the second
transports it to any remote vertex at distance two.

In the normalized case, the initial core and actor normalize the join of
the two modules. The residual-supplement lemma puts the next residual
core in that normalizer. Its action on the other two neighbors makes the
join equal to the full initial neighborhood module. Edge generation then
makes both adjacent stabilizers normalize this nontrivial two-subgroup,
contrary to the trivial ambient two-core. Conjugation transports each
stabilizer, module, commutator, and generating equality for the wrapper.

This is the common-normality contradiction in (9.4)(4), printed p.51 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement
universe u

private theorem normalizes_sup_of_commutator_le {G : Type*} [Group G] (U V D : Subgroup G)
    (hDU : D ≤ Subgroup.normalizer (U : Set G))
    (hcomm : ⁅V,D⁆ ≤ U) : D ≤ Subgroup.normalizer ((U ⊔ V : Subgroup G) : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro actor hactor element helement
  have hmap : (U ⊔ V).map (MulAut.conj actor).toMonoidHom ≤ U ⊔ V := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro point ⟨original, horiginal, rfl⟩
      exact (le_sup_left : U ≤ U ⊔ V) ((Subgroup.mem_normalizer_iff.mp (hDU hactor) original).mp horiginal)
    · rintro point ⟨original, horiginal, rfl⟩
      have hdelta : ⁅actor,original⁆ ∈ U := by
        rw [Subgroup.commutator_comm] at hcomm
        exact hcomm (Subgroup.commutator_mem_commutator hactor horiginal)
      have hprod := (U ⊔ V).mul_mem ((le_sup_left : U ≤ U ⊔ V) hdelta) ((le_sup_right : V ≤ U ⊔ V) horiginal)
      change actor * original * actor⁻¹ ∈ U ⊔ V
      simpa only [commutatorElement_def, mul_assoc,
        inv_mul_cancel, mul_one] using hprod
  exact hmap (Subgroup.mem_map_of_mem _ helement)


public theorem nine_four_full_remote_commutator_obstruction
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (remote : ctx.Γ.Vertex)
    (hremote : remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : remote ≠ ctx.criticalPath.firstStep)
    (actor : G)
    (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep)
    (hgenerate : (GAt ctx.Γ ctx.criticalPath.a ⊓
      GAt ctx.Γ ctx.criticalPath.firstStep) ⊔ Subgroup.zpowers actor =
      GAt ctx.Γ ctx.criticalPath.firstStep) :
    ¬ ⁅VAt ctx.Γ remote, Subgroup.zpowers actor⁆ ≤
      VAt ctx.Γ ctx.criticalPath.firstStep := by
  intro hcomm
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let W := VAt Γ cp.firstStep ⊔ VAt Γ remote
  let Qa := QAt Γ cp.a
  let D := Subgroup.zpowers actor
  have hDnorm : D ≤ Subgroup.normalizer (W : Set G) :=
    normalizes_sup_of_commutator_le _ _ _
      ((Subgroup.zpowers_le.mpr hactor).trans
        (stabilizer_le_normalizer_v Γ cp.firstStep)) hcomm
  have hQanorm : Qa ≤ Subgroup.normalizer (W : Set G) :=
    (le_inf
      ((((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a cp.firstStep
        ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) default).2.2).trans
        (stabilizer_le_normalizer_v Γ cp.firstStep))
      ((((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a remote
        hremote default).2.2).trans (stabilizer_le_normalizer_v Γ remote))).trans
          (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hRnorm : twoCoreIn (EAt Γ cp.firstStep) ≤ Subgroup.normalizer (W : Set G) :=
    (twoCoreIn_le _).trans
      ((nine_four_residual_le_core_actor_join ctx hb actor hactor hgenerate).trans
        (sup_le hQanorm hDnorm))
  obtain ⟨hW, hinitial⟩ := nine_four_initial_neighborhood_eq_join
    ctx hb remote hremote hne hRnorm
  have hnext : GAt Γ cp.firstStep ≤ Subgroup.normalizer (W : Set G) := by
    rw [← hgenerate]
    exact sup_le (inf_le_left.trans hinitial) hDnorm
  have hlong : 2 < cp.length := by
    have hodd := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).odd_distance
    change 1 < cp.length at hb
    obtain ⟨k, hk⟩ := hodd
    omega
  change GeneratedNeighborhoodV Γ cp.a = W at hW
  have hWtwo : IsPGroup 2 W := by
    rw [← hW]
    exact nine_seven_subgroup_isTwoGroup_of_le_vertex_core Γ cp.a _
      (nine_seven_neighborhood_le_own_core ctx.toLocalContext hlong cp.a)
  have hbot := nine_seven_edge_invariant_two_subgroup_eq_bot ctx.sectionSeven Γ
    cp.firstStep_adj W hWtwo hinitial hnext
  have hZa : ZAt Γ cp.a ≤ W :=
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1.trans le_sup_left
  have hZbot : ZAt Γ cp.a = ⊥ := bot_unique (hZa.trans_eq hbot)
  have hfour := (lemma_nine_three_ambient ctx hb cp.a ⟨1, Γ.act_one _⟩).2
  rw [hZbot, Subgroup.card_bot] at hfour
  omega

public theorem nine_four_remote_commutator_obstruction
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (remote : ctx.Γ.Vertex)
    (hdistance : ctx.Γ.distance remote ctx.criticalPath.firstStep = 2)
    (actor : G)
    (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep)
    (hgenerate : ∀ n : ctx.Γ.Vertex,
      n ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep →
      n ∈ Neighborhood ctx.Γ remote →
      (GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ n) ⊔
        Subgroup.zpowers actor = GAt ctx.Γ ctx.criticalPath.firstStep) :
    ¬ ⁅VAt ctx.Γ remote, Subgroup.zpowers actor⁆ ≤
      VAt ctx.Γ ctx.criticalPath.firstStep := by
  intro hcomm
  have hnormalize := nine_four_normalize_two_path ctx.toLocalContext remote hdistance
  dsimp only [AmbientSectionNineContext.toLocalContext] at hnormalize
  obtain ⟨neighbor, mover, hneighbor, hremote, hmover, hmove, hfix, hnew, hne⟩ := hnormalize
  let f := (MulAut.conj mover⁻¹).toMonoidHom
  have hP : (GAt ctx.Γ ctx.criticalPath.firstStep).map f =
      GAt ctx.Γ ctx.criticalPath.firstStep := by
    change (stabilizer ctx.Γ ctx.criticalPath.firstStep).map _ = _
    rw [← conjugateBy, ← stabilizer_act, hfix]
  have hU : (VAt ctx.Γ ctx.criticalPath.firstStep).map f =
      VAt ctx.Γ ctx.criticalPath.firstStep := by
    change (v ctx.Γ ctx.criticalPath.firstStep).map _ = _
    rw [← v_act, hfix]
  have hN : (GAt ctx.Γ neighbor).map f = GAt ctx.Γ ctx.criticalPath.a := by
    change (stabilizer ctx.Γ neighbor).map _ = _
    rw [← conjugateBy, ← stabilizer_act, hmove]
  have hV : (VAt ctx.Γ remote).map f = VAt ctx.Γ (ctx.Γ.act mover remote) :=
    (v_act ctx.Γ mover remote).symm
  have hactor' : f actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep := by
    rw [← hP]
    exact Subgroup.mem_map_of_mem f hactor
  have hgenerate' := congrArg (fun K : Subgroup G => K.map f)
    (hgenerate neighbor hneighbor hremote)
  rw [Subgroup.map_sup, Subgroup.map_inf _ _ f (MulAut.conj mover⁻¹).injective,
    hP, hN, MonoidHom.map_zpowers, inf_comm] at hgenerate'
  have hcomm' := Subgroup.map_mono (f := f) hcomm
  rw [Subgroup.map_commutator, hV, MonoidHom.map_zpowers, hU] at hcomm'
  exact nine_four_full_remote_commutator_obstruction ctx hb
    (ctx.Γ.act mover remote) hnew hne (f actor) hactor' hgenerate' hcomm'

end Stellmacher.SectionNine
