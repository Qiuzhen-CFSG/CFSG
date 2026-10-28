module
public import Stellmacher.SectionEight.EightFourSourceNineActorIndex
public import Stellmacher.SectionEight.EightFourSourceNineCommutingCore

/-!
# Reductions for the last case of Stellmacher (8.4)

The actual shifted actor index and source (9) give index two for the
selected edge-fixed subgroup over the middle vertex center. Restricted
commutation selects a neighboring edge-fixed subgroup outside the shifted
stabilizer. Its centralizer in the actor/core intersection is contained in
both endpoint centers. All families, configurations, and witnesses remain
the original ones. These reductions do not assert the final normality.

Source: Journal of Algebra 190 (1997), printed p.40, (8.4), last paragraph.

All reductions hold over the actual local context and source-nine record.
The local proofs preserve the selected vertices and actions; their canonical
wrappers retain the original variable context and each theorem's individual
hypotheses. The generic normalizer and index-two arguments remain unchanged.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

/-- The neighboring core normalizes an equivariant edge-fixed subgroup. -/
public theorem eight_four_neighbor_core_normalizes_edge_fixed_local
    {H : Type u} [Group H] [Finite H] {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (vertex neighbor : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent vertex neighbor) :
    QAt ctx.Γ neighbor ≤ Subgroup.normalizer (F vertex neighbor : Set H) := by
  have hvertex : QAt ctx.Γ neighbor ≤ GAt ctx.Γ vertex :=
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core neighbor vertex
      ((SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr
        (ctx.Γ.adjacent_symm hadj)) default).2.2
  have hneighbor : QAt ctx.Γ neighbor ≤ GAt ctx.Γ neighbor := by
    rw [show QAt ctx.Γ neighbor = twoCoreAmbient (GAt ctx.Γ neighbor) from
      ctx.Γ.twoCoreAt_def neighbor]
    exact Subgroup.map_subtype_le _
  exact (le_inf hvertex hneighbor).trans
    (eight_four_equivariant_edge_fixed_normalizer ctx.Γ F hcov vertex neighbor)

private theorem sup_inf_eq_of_index_two
    {H : Type u} [Group H] (C K P : Subgroup H)
    (hKC : K ≤ C) (hKP : ¬ K ≤ P) (hindex : (C ⊓ P).relIndex C = 2) :
    K ⊔ (C ⊓ P) = C := by
  let joined := K ⊔ (C ⊓ P)
  have hjoined : joined ≤ C := sup_le hKC inf_le_left
  have hdiv : joined.relIndex C ∣ 2 :=
    hindex ▸ Subgroup.relIndex_dvd_of_le_left C (show C ⊓ P ≤ joined from le_sup_right)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
  · exact le_antisymm hjoined (Subgroup.relIndex_eq_one.mp hone)
  · have hprod := Subgroup.relIndex_mul_relIndex (C ⊓ P) joined C le_sup_right hjoined
    rw [hindex, htwo] at hprod
    have hone : (C ⊓ P).relIndex joined = 1 := by omega
    exact (hKP (le_sup_left.trans ((Subgroup.relIndex_eq_one.mp hone).trans inf_le_right))).elim

section LocalProof

variable {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineLocalData ctx F)
    (hlen : 2 < ctx.criticalPath.length)

private theorem middle_adjacent : ctx.Γ.adjacent ctx.criticalPath.a' configuration.d := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hpos := cp.length_pos
  have hprevious : Γ.adjacent cp.a' (cp.path ⟨cp.length - 1, by omega⟩) := by
    have hedge := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hindex : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      dsimp
      omega
    rw [hindex, cp.path_end] at hedge
    exact Γ.adjacent_symm hedge
  have hfix : Γ.act configuration.x⁻¹ cp.a' = cp.a' := by
    have hmem := (GAt Γ cp.a').inv_mem (configuration.hL0 configuration.hx)
    change configuration.x⁻¹ ∈ (Γ.vertexStabilizer cp.a' : Set H) at hmem
    rwa [Γ.stabilizer_def] at hmem
  have hedge := adjacent_act Γ configuration.x⁻¹ hprevious
  rwa [hfix, ← configuration.hd] at hedge

include hcenter w hbranch hbase hcov hsub hformula hlen

omit hbranch hformula hlen in
/-- The source-(9) fixed subgroup meets the first-step core in the middle center. -/
public theorem eight_four_source_nine_fixed_core_intersection_local :
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    F next configuration.d ⊓ QAt ctx.Γ ctx.criticalPath.firstStep =
      ZAt ctx.Γ configuration.d := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act configuration.y⁻¹ cp.a'
  let h := ctx.sectionSeven
  have hadj := middle_adjacent ctx F configuration
  have hcentral := eight_four_terminal_neighbor_central_local ctx hcenter configuration.d hadj
  have hfixed : ZAt Γ configuration.d ≤ F next configuration.d :=
    eight_four_central_vertex_le_edge_fixed_local ctx hcenter w F hbase hcov
      next configuration.d (Γ.adjacent_symm configuration.hadj) hcentral
  have hZend : ZAt Γ configuration.d ≤ ZAt Γ cp.a' :=
    (eight_four_central_vertex_le_edge_fixed_local ctx hcenter w F hbase hcov
      cp.a' configuration.d hadj hcentral).trans ((hsub cp.a' configuration.d).trans inf_le_left)
  have hZcore : ZAt Γ configuration.d ≤ QAt Γ cp.firstStep :=
    hZend.trans ((opposite_center_le_opposite_closure_local ctx).trans
      (opposite_closure_le_next_core_local ctx))
  have hQinitial : QAt Γ cp.firstStep ≤ GAt Γ cp.a :=
    ((lemma_seven_three h Γ).sylow_and_core cp.firstStep cp.a
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
        (Γ.adjacent_symm cp.firstStep_adj)) default).2.2
  exact le_antisymm ((inf_le_inf_left _ hQinitial).trans configuration.forward)
    (le_inf hfixed hZcore)

omit hformula hlen in
/-- Containment of the selected fixed subgroup in the original endpoint is impossible. -/
public theorem eight_four_source_nine_fixed_not_le_terminal_local :
    ¬ F (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') configuration.d ≤
      ZAt ctx.Γ ctx.criticalPath.a' := by
  let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
  have heq := eight_four_source_nine_fixed_core_intersection_local ctx hcenter w
    F hbase hcov hsub configuration
  have hcentral := eight_four_terminal_neighbor_central_local ctx hcenter configuration.d
    (middle_adjacent ctx F configuration)
  intro hle
  have hcore := hle.trans ((opposite_center_le_opposite_closure_local ctx).trans
    (opposite_closure_le_next_core_local ctx))
  apply eight_four_edge_fixed_not_le_central_vertex_local ctx hcenter w hbranch F hbase hcov
    next configuration.d (ctx.Γ.adjacent_symm configuration.hadj) hcentral
  exact (le_inf le_rfl hcore).trans_eq heq

/-- The fixed subgroup has exactly twice the order of the middle vertex center. -/
public theorem eight_four_source_nine_fixed_center_index_local :
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    (ZAt ctx.Γ configuration.d).relIndex (F next configuration.d) = 2 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act configuration.y⁻¹ cp.a'
  have heq := eight_four_source_nine_fixed_core_intersection_local ctx hcenter w
    F hbase hcov hsub configuration
  have hactor := eight_four_source_nine_actor_index_local ctx hcenter w hbranch
    F hbase hcov hsub hformula configuration hlen
  change (ZAt Γ next ⊓ QAt Γ cp.firstStep).relIndex (ZAt Γ next) = 2 at hactor
  change F next configuration.d ⊓ QAt Γ cp.firstStep = ZAt Γ configuration.d at heq
  rw [Subgroup.inf_relIndex_left] at hactor
  have hbound := Subgroup.relIndex_le_of_le_right
    ((hsub next configuration.d).trans inf_le_left) (by rw [hactor]; decide)
  have hindex : (ZAt Γ configuration.d).relIndex (F next configuration.d) ≤ 2 := by
    rw [← heq, Subgroup.inf_relIndex_left]
    exact hbound.trans_eq hactor
  have hpositive : (ZAt Γ configuration.d).relIndex (F next configuration.d) ≠ 0 :=
    ne_zero_of_dvd_ne_zero Nat.card_pos.ne' (Subgroup.relIndex_dvd_card _ _)
  have hcentral := eight_four_terminal_neighbor_central_local ctx hcenter configuration.d
    (middle_adjacent ctx F configuration)
  have hne : (ZAt Γ configuration.d).relIndex (F next configuration.d) ≠ 1 := by
    intro hone
    exact eight_four_edge_fixed_not_le_central_vertex_local ctx hcenter w hbranch F hbase hcov
      next configuration.d (Γ.adjacent_symm configuration.hadj) hcentral
      (Subgroup.relIndex_eq_one.mp hone)
  change (ZAt Γ configuration.d).relIndex (F next configuration.d) = 2
  omega

/-- The actual actor-index theorem rules out the commuting-core case. -/
public theorem eight_four_source_nine_noncommuting_core_local :
    ⁅(⨆ vertex, F vertex ctx.criticalPath.firstStep),
      ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') ⊓
        QAt ctx.Γ ctx.criticalPath.firstStep⁆ ≠ ⊥ :=
  eight_four_source_nine_noncommuting_core_of_actor_index_local ctx hcenter w hbranch
    F hbase hcov hsub hformula configuration hlen
    (eight_four_source_nine_actor_index_local ctx hcenter w hbranch
      F hbase hcov hsub hformula configuration hlen)

/-- A neighboring fixed subgroup escapes the shifted endpoint stabilizer. -/
public theorem eight_four_source_nine_exists_escaping_neighbor_local :
    ∃ vertex, ctx.Γ.adjacent vertex ctx.criticalPath.firstStep ∧
      ¬ F vertex ctx.criticalPath.firstStep ≤
        GAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') := by
  classical
  have hrestricted := eight_four_source_nine_restricted_commutation_local ctx hcenter w hbranch
    F hbase hcov hsub hformula configuration hlen
  have hnot := (eight_four_source_nine_index_two_of_restricted_commutation_local
    ctx hcenter w hbranch F hbase hcov hsub hformula configuration hlen hrestricted).1
  have hex : ∃ vertex, ¬ F vertex ctx.criticalPath.firstStep ≤
      GAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') := by
    by_contra hnone
    push Not at hnone
    exact hnot (iSup_le hnone)
  obtain ⟨vertex, hescape⟩ := hex
  refine ⟨vertex, ?_, hescape⟩
  by_contra hnonadj
  apply hescape
  rw [hformula]
  apply iSup_le
  intro actor
  apply iSup_le
  intro htransport
  have hedge := adjacent_act ctx.Γ actor ctx.criticalPath.firstStep_adj
  rw [htransport.1, htransport.2] at hedge
  exact (hnonadj hedge).elim

/-- The selected seed's centralizer lies in both shifted and original endpoint centers. -/
public theorem eight_four_source_nine_seed_centralizer_le_intersection_local
    (vertex : ctx.Γ.Vertex)
    (hescape : ¬ F vertex ctx.criticalPath.firstStep ≤
      GAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a')) :
    (ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') ⊓
      QAt ctx.Γ ctx.criticalPath.firstStep) ⊓
        Subgroup.centralizer (F vertex ctx.criticalPath.firstStep : Set H) ≤
      ZAt ctx.Γ ctx.criticalPath.a' ⊓
        ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act configuration.y⁻¹ cp.a'
  let C := ⨆ point, F point cp.firstStep
  let U := (ZAt Γ next ⊓ QAt Γ cp.firstStep) ⊓
    Subgroup.centralizer (F vertex cp.firstStep : Set H)
  let h := ctx.sectionSeven
  have hrestricted := eight_four_source_nine_restricted_commutation_local ctx hcenter w hbranch
    F hbase hcov hsub hformula configuration hlen
  have hdata := eight_four_source_nine_index_two_of_restricted_commutation_local
    ctx hcenter w hbranch F hbase hcov hsub hformula configuration hlen hrestricted
  have hcard : Nat.card C = 2 * Nat.card ↥(C ⊓ GAt Γ next) := by
    rw [← hdata.2.2.1]
    exact hdata.2.2.2
  have hprod := (C ⊓ GAt Γ next).subgroupOf C |>.card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show C ⊓ GAt Γ next ≤ C from inf_le_left)).toEquiv] at hprod
  change Nat.card ↥(C ⊓ GAt Γ next) * (C ⊓ GAt Γ next).relIndex C = Nat.card C at hprod
  have hpositive : 0 < Nat.card ↥(C ⊓ GAt Γ next) := Nat.card_pos
  have hindex : (C ⊓ GAt Γ next).relIndex C = 2 := by nlinarith
  have hgen := sup_inf_eq_of_index_two C (F vertex cp.firstStep) (GAt Γ next)
    (le_iSup (fun point => F point cp.firstStep) vertex) hescape hindex
  have hUC : U ≤ Subgroup.centralizer (C : Set H) := by
    apply Subgroup.le_centralizer_iff.mpr
    rw [← hgen]
    refine sup_le (Subgroup.le_centralizer_iff.mp inf_le_right) ?_
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hrestricted).trans
      (Subgroup.centralizer_le (show U ≤ ZAt Γ next from inf_le_left.trans inf_le_left))
  have hUQ : U ≤ Subgroup.centralizer (QAt Γ next : Set H) :=
    (show U ≤ ZAt Γ next from inf_le_left.trans inf_le_left).trans
      (((lemma_seven_three h Γ).center_core next configuration.d
        ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
          (Γ.adjacent_symm configuration.hadj))).trans
        ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
          (SevenSix.centerAmbient_le_centralizer _)))
  have hUL : U ≤ Subgroup.centralizer (configuration.Ltilde : Set H) := by
    apply Subgroup.le_centralizer_iff.mpr
    rw [hdata.2.1]
    exact sup_le (Subgroup.le_centralizer_iff.mp hUC) (Subgroup.le_centralizer_iff.mp hUQ)
  refine le_inf ?_ (inf_le_left.trans inf_le_left)
  intro point hpoint
  have hpointNext : point ∈ ZAt Γ next := hpoint.1.1
  have htransport : ZAt Γ next = (ZAt Γ cp.a').conjBy configuration.y := by
    change z Γ (Γ.act configuration.y⁻¹ cp.a') = _
    rw [z_act, inv_inv]
    rfl
  rw [htransport] at hpointNext
  obtain ⟨preimage, hpreimage, heq⟩ := hpointNext
  have hfix := Subgroup.mem_centralizer_iff.mp (hUL hpoint) configuration.y configuration.hy
  have hsame : preimage = point := by
    change configuration.y * preimage * configuration.y⁻¹ = point at heq
    have hsolve := congrArg (fun value => configuration.y⁻¹ * value * configuration.y) heq
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] at hsolve
    rw [← hfix, inv_mul_cancel_left] at hsolve
    exact hsolve
  exact hsame ▸ hpreimage

end LocalProof

/-! The original canonical variable context is retained for exact API wrappers. -/

section CanonicalProof

variable {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (hsub : ∀ d l, F d l ≤ ZAt ctx.Γ d ⊓ GAt ctx.Γ l)
    (hformula : ∀ d l, F d l = ⨆ (g : H)
      (_ : ctx.Γ.act g ctx.criticalPath.a = d ∧
        ctx.Γ.act g ctx.criticalPath.firstStep = l),
      (w.oneJFixedPoints S).conjBy g⁻¹)
    (configuration : EightFourSourceNineData ctx F)
    (hlen : 2 < ctx.criticalPath.length)

include hcenter w hbranch hbase hcov hsub hformula hlen

omit hbranch hformula hlen in
public theorem eight_four_source_nine_fixed_core_intersection :
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    F next configuration.d ⊓ QAt ctx.Γ ctx.criticalPath.firstStep =
      ZAt ctx.Γ configuration.d := by
  exact eight_four_source_nine_fixed_core_intersection_local ctx.toLocalContext hcenter w F hbase hcov hsub configuration.toLocal

omit hformula hlen in
public theorem eight_four_source_nine_fixed_not_le_terminal :
    ¬ F (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') configuration.d ≤
      ZAt ctx.Γ ctx.criticalPath.a' := by
  exact eight_four_source_nine_fixed_not_le_terminal_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub configuration.toLocal

public theorem eight_four_source_nine_fixed_center_index :
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    (ZAt ctx.Γ configuration.d).relIndex (F next configuration.d) = 2 := by
  exact eight_four_source_nine_fixed_center_index_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula configuration.toLocal hlen

public theorem eight_four_source_nine_noncommuting_core :
    ⁅(⨆ vertex, F vertex ctx.criticalPath.firstStep),
      ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') ⊓
        QAt ctx.Γ ctx.criticalPath.firstStep⁆ ≠ ⊥ := by
  exact eight_four_source_nine_noncommuting_core_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula configuration.toLocal hlen

public theorem eight_four_source_nine_exists_escaping_neighbor :
    ∃ vertex, ctx.Γ.adjacent vertex ctx.criticalPath.firstStep ∧
      ¬ F vertex ctx.criticalPath.firstStep ≤
        GAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') := by
  exact eight_four_source_nine_exists_escaping_neighbor_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula configuration.toLocal hlen

public theorem eight_four_source_nine_seed_centralizer_le_intersection
    (vertex : ctx.Γ.Vertex)
    (hescape : ¬ F vertex ctx.criticalPath.firstStep ≤
      GAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a')) :
    (ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') ⊓
      QAt ctx.Γ ctx.criticalPath.firstStep) ⊓
        Subgroup.centralizer (F vertex ctx.criticalPath.firstStep : Set H) ≤
      ZAt ctx.Γ ctx.criticalPath.a' ⊓
        ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a') := by
  exact eight_four_source_nine_seed_centralizer_le_intersection_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula configuration.toLocal hlen vertex hescape

end CanonicalProof

end Stellmacher.SectionEight
