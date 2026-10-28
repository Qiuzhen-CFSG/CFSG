module
public import Stellmacher.SectionTen.TenOneCommonIntersection
public import Stellmacher.SectionTen.TenOneGeneratedContainment
public import Stellmacher.SectionFiveToSeven.NeighborCenterNormalizer
public import Stellmacher.SectionNine.NineThreeOrbitEdgeCoreCentralizer
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# The small-module derived equality in Stellmacher (10.1)

In the actual ambient Section Ten geometry, suppose that the first-step
module has order eight, the small case supplied by (9.5). Its intersection
with the terminal module is the middle center of order four. The actual
generated subgroup W also equals that center, and the derived subgroup of
the generated neighborhood is exactly the intersection.

Critical noncontainment makes both the module intersection and the seed
proper in the order-eight module. They contain the middle four-center, so
finite cardinalities identify them with that center. Stabilizer invariance
then identifies the conjugate closure W. The common-intersection theorem
bounds the derived subgroup inside the middle center. It is nontrivial,
because an abelian neighborhood group would put the first module inside
the full terminal-module centralizer and hence the terminal core. Finally,
an invariant line in the middle four-center is impossible: its normalizer
centralizes it; a distinct neighboring center line would force the neighbor
core to centralize the whole four-center and lie in the middle core. Equality
with that neighboring line contradicts the neighbor-center normalizer theorem.
Thus the derived subgroup has order four and fills the center.

Source: Stellmacher, Journal of Algebra 190 (1997), (10.1), printed p.60,
alternative (6) and the following equalities in `refs/files/stellmacher-n-group.pdf`.
The order-eight hypothesis is an actual source case, not a derived conclusion
or an assumption about the generated subgroups.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem core_le_self
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (vertex : ctx.Γ.Vertex) : QAt ctx.Γ vertex ≤ GAt ctx.Γ vertex := by
  rw [QAt, q, ctx.Γ.twoCoreAt_def]
  exact twoCoreIn_le _

/-- The middle four-center has no invariant subgroup of order two. This
uses only the standing Section Ten geometry, without a small-module case. -/
public theorem ten_one_no_invariant_middle_line
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (U : Subgroup G) (hU : U ≤ ZAt ctx.Γ middle)
    (hnorm : GAt ctx.Γ middle ≤ Subgroup.normalizer (U : Set G)) :
    Nat.card U ≠ 2 := by
  intro hcard
  obtain ⟨horbit, hfirst, _, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hopen := sectionTenOpeningData ctx middle hpath
  let P := GAt ctx.Γ middle
  let Z := ZAt ctx.Γ middle
  let L := ZAt ctx.Γ ctx.criticalPath.firstStep
  let Q := QAt ctx.Γ ctx.criticalPath.firstStep
  have hZQ : Z ≤ QAt ctx.Γ middle := by
    rw [show Z = omegaOneCenter (QAt ctx.Γ middle) from hopen.center_omega]
    exact Subgroup.map_subtype_le _
  have hUP : U ≤ P := hU.trans (hZQ.trans (core_le_self ctx middle))
  let _ : (U.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUP).mpr hnorm
  have hcentral := Subgroup.central_of_normal_card_two (U.subgroupOf P)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUP).toEquiv]; exact hcard)
  have hPC : P ≤ Subgroup.centralizer (U : Set G) := by
    intro actor hactor
    rw [Subgroup.mem_centralizer_iff]
    intro element helement
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp
      (hcentral (show (⟨element, hUP helement⟩ : P) ∈ U.subgroupOf P from helement))
      (⟨actor, hactor⟩ : P))).symm
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hfour := (lemma_nine_three_ambient ctx.toAmbientSectionNineContext hb
    ctx.criticalPath.a ⟨1, ctx.Γ.act_one _⟩).2
  have hLcard : Nat.card L = 2 := nine_next_center_order_of_initial_four
    ctx.toLocalContext.toSectionNineLocalContext hfour
  have hLZ : L ≤ Z := by
    dsimp only [L, Z]
    rw [hopen.center_direct_product.1]
    exact le_sup_left
  have hQP : Q ≤ P := ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core
    ctx.criticalPath.firstStep middle
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hfirst)) default).2.2
  have hQL : Q ≤ Subgroup.centralizer (L : Set G) := by
    apply Subgroup.le_centralizer_iff.mpr
    exact ((lemma_seven_three ctx.sectionSeven ctx.Γ).center_core
      ctx.criticalPath.firstStep middle
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hfirst))).trans
        ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  have hUL : U ≤ L := by
    by_contra hnot
    have hsup : U ⊔ L = Z := by
      have hle : U ⊔ L ≤ Z := sup_le hU hLZ
      have hlt : Nat.card L < Nat.card (U ⊔ L : Subgroup G) := by
        apply lt_of_le_of_ne (Subgroup.card_le_of_le le_sup_right)
        intro heq
        exact hnot (le_sup_left.trans
          (Subgroup.eq_of_le_of_card_ge le_sup_right heq.ge).ge)
      have hdiv := Subgroup.card_dvd_of_le (show L ≤ U ⊔ L from le_sup_right)
      rw [hLcard] at hlt hdiv
      obtain ⟨factor, hfactor⟩ := hdiv
      apply Subgroup.eq_of_le_of_card_ge hle
      have hzcard : Nat.card Z = 4 := hopen.center_card
      omega
    have hQcentral : Q ≤ Subgroup.centralizer (Z : Set G) := by
      rw [← hsup]
      apply Subgroup.le_centralizer_iff.mpr
      exact sup_le (Subgroup.le_centralizer_iff.mp (hQP.trans hPC))
        (Subgroup.le_centralizer_iff.mp hQL)
    have hQtwo : IsPGroup 2 Q := by
      change IsPGroup 2 (ctx.Γ.twoCoreAt ctx.criticalPath.firstStep)
      rw [ctx.Γ.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2) (G := GAt ctx.Γ ctx.criticalPath.firstStep)).map _
    have hcontained := nine_three_orbit_pgroup_centralizer
      ctx.toLocalContext.toSectionNineLocalContext middle horbit Q hQtwo hQP hQcentral
    have hescape := nine_seven_residual_core_escapes_neighbor
      ctx.toLocalContext.toSectionNineLocalContext ctx.criticalPath.firstStep middle
      ⟨1, ctx.Γ.act_one _⟩ (ctx.Γ.adjacent_symm hfirst)
    apply hescape
    apply le_trans ?_ hcontained
    change twoCoreIn (ctx.Γ.twoResidualAt ctx.criticalPath.firstStep) ≤
      ctx.Γ.twoCoreAt ctx.criticalPath.firstStep
    rw [ctx.Γ.twoResidualAt_def, ctx.Γ.twoCoreAt_def, residual_core_eq_inter_core]
    exact inf_le_right
  have hULeq : U = L := Subgroup.eq_of_le_of_card_ge hUL (by omega)
  apply neighbor_center_not_normalized ctx.sectionSeven ctx.Γ middle
    ctx.criticalPath.firstStep ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst)
  rwa [hULeq] at hnorm

public theorem ten_one_small_intersection
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8) :
    VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a' =
      ZAt ctx.Γ middle := by
  obtain ⟨_, hfirst, hterminal, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hopen := sectionTenOpeningData ctx middle hpath
  have hZ := le_inf
    (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hfirst))
    (nine_seven_neighbor_center_le_module ctx.Γ (ctx.Γ.adjacent_symm hterminal))
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hVQ := neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath hb ctx.criticalPath.a'
  have hproper : ¬ VAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a' :=
    fun h => hopen.first_noncontainment (h.trans hVQ)
  have hlt : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
      VAt ctx.Γ ctx.criticalPath.a' : Subgroup G) < 8 := by
    rw [← hsmall]
    apply lt_of_le_of_ne (Subgroup.card_le_of_le inf_le_left)
    intro heq
    exact hproper ((Subgroup.eq_of_le_of_card_ge inf_le_left heq.ge).ge.trans inf_le_right)
  have hdiv := Subgroup.card_dvd_of_le hZ
  rw [hopen.center_card] at hdiv
  obtain ⟨factor, hfactor⟩ := hdiv
  symm
  exact Subgroup.eq_of_le_of_card_ge hZ (by rw [hopen.center_card]; omega)

public theorem ten_one_small_derived
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8) :
    DerivedAmbient (GeneratedNeighborhoodV ctx.Γ middle) =
      VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ ctx.criticalPath.a' := by
  let W := GeneratedNeighborhoodV ctx.Γ middle
  let D := DerivedAmbient W
  have hDZ : D ≤ ZAt ctx.Γ middle :=
    (ten_one_generated_derived_le_intersection ctx middle hpath).trans_eq
      (ten_one_small_intersection ctx middle hpath hsmall)
  obtain ⟨_, hfirst, hterminal, _⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hopen := sectionTenOpeningData ctx middle hpath
  have hDnorm : GAt ctx.Γ middle ≤ Subgroup.normalizer (D : Set G) := by
    intro actor hactor
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hD : D = ⁅W, W⁆ := Subgroup.map_subtype_commutator W
    rw [hD]
    have hWmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (nine_seven_stabilizer_normalizes_neighborhood ctx.Γ middle hactor)
    rw [Subgroup.map_commutator, hWmap]
  have hDne : D ≠ ⊥ := by
    intro hbot
    have hzero : ⁅W, W⁆ = ⊥ := by
      change (_root_.commutator W).map W.subtype = ⊥ at hbot
      rwa [Subgroup.map_subtype_commutator] at hbot
    have hVW (vertex : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent middle vertex) :
        VAt ctx.Γ vertex ≤ W :=
      le_sSup ⟨vertex, (mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj, rfl⟩
    have hpair : ⁅VAt ctx.Γ ctx.criticalPath.firstStep,
        VAt ctx.Γ ctx.criticalPath.a'⁆ = ⊥ :=
      le_bot_iff.mp ((Subgroup.commutator_mono (hVW _ hfirst) (hVW _ hterminal)).trans_eq hzero)
    exact hopen.first_noncontainment
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hpair).trans hopen.endpoint_centralizer)
  have hcardNeTwo := ten_one_no_invariant_middle_line ctx middle hpath D hDZ hDnorm
  have hpositive := (Subgroup.one_lt_card_iff_ne_bot D).mpr hDne
  have hdiv := Subgroup.card_dvd_of_le hDZ
  rw [hopen.center_card] at hdiv
  have hbound := Nat.le_of_dvd (by decide : 0 < 4) hdiv
  have hcard : Nat.card D = 4 := by
    interval_cases h : Nat.card D <;> norm_num at *
  rw [ten_one_small_intersection ctx middle hpath hsmall]
  exact Subgroup.eq_of_le_of_card_ge hDZ (by rw [hcard, hopen.center_card])

public theorem ten_one_small_generated_eq_center
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8) :
    conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ middle) = ZAt ctx.Γ middle := by
  let U := VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a'
  have hopen := sectionTenOpeningData ctx middle hpath
  have hintersection := ten_one_small_intersection ctx middle hpath hsmall
  have hb : 1 < ctx.criticalPath.length := by rw [ctx.critical_length]; decide
  have hZU : ZAt ctx.Γ middle ≤ U := by
    rw [← hintersection]
    exact inf_le_inf_left _
      (neighbor_join_le_core_of_length_gt_one ctx.Γ ctx.criticalPath hb ctx.criticalPath.a')
  have hlt : Nat.card U < 8 := by
    rw [← hsmall]
    apply lt_of_le_of_ne (Subgroup.card_le_of_le (show U ≤ VAt ctx.Γ ctx.criticalPath.firstStep from inf_le_left))
    intro heq
    exact hopen.first_noncontainment
      ((Subgroup.eq_of_le_of_card_ge inf_le_left heq.ge).ge.trans inf_le_right)
  have hdiv := Subgroup.card_dvd_of_le hZU
  rw [hopen.center_card] at hdiv
  obtain ⟨factor, hfactor⟩ := hdiv
  have hUeq : U = ZAt ctx.Γ middle :=
    (Subgroup.eq_of_le_of_card_ge hZU (by rw [hopen.center_card]; omega)).symm
  change conjugateClosure U (GAt ctx.Γ middle) = ZAt ctx.Γ middle
  rw [hUeq]
  apply le_antisymm
  · rw [conjugateClosure, Subgroup.closure_le]
    rintro element ⟨actor, generator, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (stabilizer_le_normalizer_z ctx.Γ middle actor.property) generator).mp generator.property
  · intro element helement
    apply Subgroup.subset_closure
    refine ⟨1, ⟨element, helement⟩, ?_⟩
    simp

end Stellmacher.SectionTen
