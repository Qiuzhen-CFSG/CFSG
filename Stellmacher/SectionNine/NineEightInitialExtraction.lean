module
public import Stellmacher.SectionNine.NineEightTerminalContainment
public import Stellmacher.SectionNine.NineEightCoreNeighbor

/-!
# The first neighborhood-join extraction in Stellmacher (9.8)

Under the actual (9.8) terminal-center containment and critical length greater
than three, a terminal neighbor m cuts the initial neighborhood join W with
index two. The initial center escapes its stabilizer and does not commute
with its center. The strongest theorem retains generation of the terminal stabilizer by
the new edge and every subgroup of W crossing that edge. This includes
the initial-center generation needed for the symmetric extraction. The original W-generation
form is preserved as a wrapper.

The center generators of abelian W have exponent two, so W is elementary.
The post-(9.3) center splitting gives centralization of the penultimate
center; the proved terminal containment and normalized-subgroup Sylow
conjugacy place W in a terminal neighbor core. Criticality supplies a
prescribed initial-center actor outside the terminal core. Apply the proved
prescribed-actor portion of (7.8) and its geometric conversion. The latter
identifies the coatom with W intersect G_m. If the two centers commuted,
the prescribed actor and the conjugate of W would centralize Z_m. Their
generation would force forbidden normalization of a neighboring center.
The prescribed actor lies in the initial center, while the conjugated W lies
in the extracted edge; their generation gives the stronger center/edge join.

Source: B. Stellmacher, Journal of Algebra 190 (1997), (9.8), printed p.55,
first displayed formula. The local refs/latex/stellmacher-n-group.tex
abridges this proof. No full (7.8) placeholder or later (9.8) conclusion
is consumed.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped IsMulCommutative
universe u

private theorem neighborhood_elementary
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 4 < ctx.criticalPath.length) (vertex : ctx.Γ.Vertex) :
    IsElementaryAbelian 2 (GeneratedNeighborhoodV ctx.Γ vertex) := by
  let W := GeneratedNeighborhoodV ctx.Γ vertex
  let _ : IsMulCommutative W := nine_eight_neighborhood_abelian ctx hb vertex
  let K := (powMonoidHom 2 : W →* W).ker
  have hWK : W ≤ K.map W.subtype := by
    apply nine_eight_generated_neighborhood_le
    intro middle hmiddle endpoint hendpoint
    have hcenterW : ZAt ctx.Γ endpoint ≤ W := by
      apply (show ZAt ctx.Γ endpoint ≤ VAt ctx.Γ middle from ?_).trans
        (nine_eight_v_le_generated_neighborhood ctx.Γ hmiddle)
      change z ctx.Γ endpoint ≤ v ctx.Γ middle
      rw [v, ctx.Γ.vAt_def]
      exact le_sSup ⟨endpoint, hendpoint, rfl⟩
    let _ : IsElementaryAbelian 2 (ZAt ctx.Γ endpoint) :=
      z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ
        ((mem_neighborhood_iff_adjacent ctx.Γ).mpr
          (ctx.Γ.adjacent_symm ((mem_neighborhood_iff_adjacent ctx.Γ).mp hendpoint)))
    intro element helement
    refine ⟨⟨element, hcenterW helement⟩, ?_, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian element helement
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro element
  obtain ⟨inside, hinside, heq⟩ := hWK element.property
  have hpow := MonoidHom.mem_ker.mp hinside
  change inside ^ 2 = 1 at hpow
  have hequal : inside = element := Subtype.ext heq
  rwa [hequal] at hpow

private theorem initial_neighborhood_extraction_inputs
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcontain : ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep) :
    ∃ neighbor : ctx.Γ.Vertex,
      neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a' ∧
      GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a ≤ QAt ctx.Γ neighbor := by
  let cp := ctx.criticalPath
  have hlong : 4 < cp.length := by
    have hge := nine_ten_length_ge_five ctx.toLocalContext hb
    change 5 ≤ cp.length at hge
    omega
  let previous := cp.path ⟨cp.length - 2, by omega⟩
  let middle := cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hleft : ctx.Γ.adjacent middle previous := by
    apply ctx.Γ.adjacent_symm
    have hedge := cp.path_adj ⟨cp.length - 2, by omega⟩
    have hindex : (⟨cp.length - 2, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hindex] at hedge
    exact hedge
  have hright : ctx.Γ.adjacent middle cp.a' := by
    have hedge := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hlast : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hlast, cp.path_end] at hedge
    exact hedge
  have hdistinct : previous ≠ cp.a' := by
    intro heq
    have hbound := path_distance_le ctx.Γ cp 0 (cp.length - 2) (by omega) (by omega)
    have hzero : (⟨0, by omega⟩ : Fin (cp.length + 1)) = 0 := Fin.ext rfl
    rw [hzero, cp.path_start, Nat.sub_zero] at hbound
    change ctx.Γ.distance cp.a previous ≤ cp.length - 2 at hbound
    rw [heq, cp.endpoint_distance] at hbound
    omega
  obtain ⟨alignment, halignInitial, halignNext⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ cp ctx.commutator_eq
  have hmiddle : IsConjugateVertex ctx.Γ cp.a middle := ⟨alignment, halignInitial⟩
  obtain ⟨actor, hactor⟩ := nine_eight_residual_transitivity ctx.sectionSeven ctx.Γ
    middle ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hright)
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hleft)
  have hprevious : IsConjugateVertex ctx.Γ cp.firstStep previous := by
    refine ⟨alignment * (actor : G), ?_⟩
    rw [ctx.Γ.act_mul, halignNext]
    exact hactor
  have hinitial : cp.a ∈ neighborhood ctx.Γ cp.firstStep :=
    (mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm cp.firstStep_adj)
  have hWprevious := nine_eight_neighborhood_le_preterminal ctx.toLocalContext
    hlong cp.a hinitial
  have hWleft := hWprevious.trans
    (nine_eight_first_orbit_center_centralizes ctx.toLocalContext previous hprevious)
  have hWright := nine_eight_neighborhood_centralizes_terminal_center
    ctx.toLocalContext hlong hcontain cp.a hinitial
  have hsplit := (nine_three_center_split ctx (by omega) hmiddle hleft hright hdistinct).1
  have hcentral : GeneratedNeighborhoodV ctx.Γ cp.a ≤
      Subgroup.centralizer (ZAt ctx.Γ middle : Set G) := by
    apply Subgroup.le_centralizer_iff.mpr
    rw [hsplit]
    exact sup_le (Subgroup.le_centralizer_iff.mp hWleft)
      (Subgroup.le_centralizer_iff.mp hWright)
  let _ : IsElementaryAbelian 2 (GeneratedNeighborhoodV ctx.Γ cp.a) :=
    neighborhood_elementary ctx.toLocalContext hlong cp.a
  exact nine_eight_core_neighbor_of_center_centralizing ctx.toLocalContext cp.a' middle
    ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hright))
    hmiddle _ (IsElementaryAbelian.isPGroup 2 _)
    (nine_eight_neighborhood_le_terminal ctx hb hcontain cp.a hinitial) hcentral

public theorem nine_eight_initial_crossing_extraction
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcontain : ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep) :
    ∃ neighbor : ctx.Γ.Vertex,
      neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a' ∧
      QuotientCardEq (GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a)
        (GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ neighbor) 2 ∧
      (¬ ZAt ctx.Γ ctx.criticalPath.a ≤ GAt ctx.Γ neighbor) ∧
      ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ neighbor⁆ ≠ ⊥ ∧
      (∀ support : Subgroup G, support ≤ GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a →
        (¬ support ≤ GAt ctx.Γ neighbor) →
        (GAt ctx.Γ ctx.criticalPath.a' ⊓ GAt ctx.Γ neighbor) ⊔ support =
          GAt ctx.Γ ctx.criticalPath.a') := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let W := GeneratedNeighborhoodV Γ cp.a
  obtain ⟨l, hl, hWcore⟩ := initial_neighborhood_extraction_inputs ctx hb hcontain
  have hlong : 4 < cp.length := by
    have hge := nine_ten_length_ge_five ctx.toLocalContext hb
    change 5 ≤ cp.length at hge
    omega
  let _ : IsElementaryAbelian 2 W := neighborhood_elementary ctx.toLocalContext hlong cp.a
  let _ : Fact (IsPGroup 2 W) := ⟨IsElementaryAbelian.isPGroup 2 W⟩
  have hPhi : frattiniAmbient W ≤ QAt Γ cp.a' := by
    rw [frattiniAmbient, frattini_eq_bot_of_isElementaryAbelian (R := W) (p := 2),
      Subgroup.map_bot]
    exact bot_le
  obtain ⟨actor, hactorZ, hactorNot⟩ := SetLike.not_le_iff_exists.mp cp.critical.2
  have hZW : ZAt Γ cp.a ≤ W :=
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1.trans
      (nine_eight_v_le_generated_neighborhood Γ
        ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj))
  have hactorW := hZW hactorZ
  have hWnot : ¬ W ≤ QAt Γ cp.a' := fun hle => hactorNot (hle hactorW)
  obtain ⟨conjugator, A0, E, hEP, _, h0W, hgen, hcard, hconjE, _, h0core,
      hedge, hmodel, _, hby, _, hactor0⟩ :=
    sevenEight_quotient_configuration_with_actor ctx.sectionSeven Γ cp.a' l hl
      W hWcore hWnot hPhi actor hactorW hactorNot
  obtain ⟨data⟩ := nine_three_geometric_extraction ctx.sectionSeven Γ cp.a' l hl
    W E A0 hWcore hPhi actor hactorW hactor0 conjugator hconjE hEP hgen h0W hcard
      h0core hedge hmodel hby
  let m := Γ.act data.x⁻¹ l
  refine ⟨m, data.neighbor, ?_, ?_, ?_, ?_⟩
  · change Nat.card W = 2 * Nat.card ↥(W ⊓ GAt Γ m)
    rw [← data.coatom_eq]
    exact data.coatom_card
  · exact fun hle => data.actor_outside (hle hactorZ)
  · intro hcomm
    have hactorC := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) hactorZ
    have hreverse : cp.a' ∈ neighborhood Γ m :=
      (mem_neighborhood_iff_adjacent Γ).mpr
        (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp data.neighbor))
    have hcenterCore : ZAt Γ m ≤ Subgroup.centralizer (QAt Γ m : Set G) :=
      ((lemma_seven_three ctx.sectionSeven Γ).center_core m cp.a' hreverse).trans
        ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
    have hconjC : W.conjBy data.x ≤ Subgroup.centralizer (ZAt Γ m : Set G) :=
      data.conjugate_core_le.trans (Subgroup.le_centralizer_iff.mp hcenterCore)
    have hEC : E ≤ Subgroup.centralizer (ZAt Γ m : Set G) := by
      rw [data.actor_generated actor hactorW data.actor_outside]
      exact sup_le ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hactorC)) hconjC
    apply neighbor_center_not_normalized ctx.sectionSeven Γ cp.a' m data.neighbor
    rw [← data.edge_generated]
    exact sup_le (hEC.trans (Subgroup.centralizer_le_normalizer _))
      (inf_le_right.trans (stabilizer_le_normalizer_z Γ m))
  · intro support hsupport hsupportNot
    obtain ⟨generator,hgenerator,hgeneratorNot⟩ := SetLike.not_le_iff_exists.mp hsupportNot
    have hreverse : cp.a' ∈ neighborhood Γ m :=
      (mem_neighborhood_iff_adjacent Γ).mpr
        (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp data.neighbor))
    have hcore : QAt Γ m ≤ GAt Γ cp.a' :=
      ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core m cp.a' hreverse default).2.2
    have hcoreSelf : QAt Γ m ≤ GAt Γ m := by
      rw [QAt,q,Γ.twoCoreAt_def]
      exact twoCoreIn_le _
    have hconj : W.conjBy data.x ≤ GAt Γ cp.a' ⊓ GAt Γ m :=
      data.conjugate_core_le.trans (le_inf hcore hcoreSelf)
    have hsupportTerminal : support ≤ GAt Γ cp.a' := hsupport.trans
      (nine_eight_neighborhood_le_terminal ctx hb hcontain cp.a
        ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)))
    apply le_antisymm (sup_le inf_le_left hsupportTerminal)
    apply data.edge_generated.ge.trans
    refine sup_le ?_ le_sup_left
    rw [data.actor_generated generator (hsupport hgenerator) hgeneratorNot]
    exact sup_le
      (((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hgenerator)).trans le_sup_right)
      (hconj.trans le_sup_left)


public theorem nine_eight_initial_center_extraction
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcontain : ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep) :
    ∃ neighbor : ctx.Γ.Vertex,
      neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a' ∧
      QuotientCardEq (GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a)
        (GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ neighbor) 2 ∧
      (¬ ZAt ctx.Γ ctx.criticalPath.a ≤ GAt ctx.Γ neighbor) ∧
      ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ neighbor⁆ ≠ ⊥ ∧
      (GAt ctx.Γ ctx.criticalPath.a' ⊓ GAt ctx.Γ neighbor) ⊔
        ZAt ctx.Γ ctx.criticalPath.a = GAt ctx.Γ ctx.criticalPath.a' := by
  obtain ⟨neighbor,hneighbor,hindex,hnot,hcomm,hgenerate⟩ :=
    nine_eight_initial_crossing_extraction ctx hb hcontain
  refine ⟨neighbor,hneighbor,hindex,hnot,hcomm,?_⟩
  have hZW : ZAt ctx.Γ ctx.criticalPath.a ≤ GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a :=
    (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.1.trans
      (nine_eight_v_le_generated_neighborhood ctx.Γ
        ((mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj))
  exact hgenerate _ hZW hnot

public theorem nine_eight_initial_neighborhood_extraction
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcontain : ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep) :
    ∃ neighbor : ctx.Γ.Vertex,
      neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a' ∧
      QuotientCardEq (GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a)
        (GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ neighbor) 2 ∧
      (¬ ZAt ctx.Γ ctx.criticalPath.a ≤ GAt ctx.Γ neighbor) ∧
      ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ neighbor⁆ ≠ ⊥ ∧
      (GAt ctx.Γ ctx.criticalPath.a' ⊓ GAt ctx.Γ neighbor) ⊔
        GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a = GAt ctx.Γ ctx.criticalPath.a' := by
  obtain ⟨neighbor,hneighbor,hindex,hnot,hcomm,hgenerate⟩ :=
    nine_eight_initial_center_extraction ctx hb hcontain
  refine ⟨neighbor,hneighbor,hindex,hnot,hcomm,?_⟩
  have hW : GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a ≤ GAt ctx.Γ ctx.criticalPath.a' :=
    nine_eight_neighborhood_le_terminal ctx hb hcontain ctx.criticalPath.a
      ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj))
  have hZW : ZAt ctx.Γ ctx.criticalPath.a ≤ GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a :=
    (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.1.trans
      (nine_eight_v_le_generated_neighborhood ctx.Γ
        ((mem_neighborhood_iff_adjacent ctx.Γ).mpr ctx.criticalPath.firstStep_adj))
  exact le_antisymm (sup_le inf_le_left hW) (hgenerate.ge.trans (sup_le_sup_left hZW _))

end Stellmacher.SectionNine
