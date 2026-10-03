module

public import Stellmacher.SectionEight.EightFourInitialFixedCommutator
public import Stellmacher.SectionEight.EightFourSourceNineConfiguration
public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.SectionFiveToSeven.PrescribedCriticalPairNormalization
public import Stellmacher.SectionFiveToSeven.CriticalPairCommutator

/-!
# The shifted commutator containment in Stellmacher (8.4)

At critical distance greater than two, extend the terminal endpoint by the
two genuine edges of the source-nine configuration. If the shifted center
does not commute with the second path center, short-path minimality makes
them a critical pair whose geodesic begins with the selected intermediate
vertex. This geometric kernel uses only the local Section Seven data.

Normalize that pair through the prescribed first edge. Its orientation is
forced by first-step centrality and noncommutation. The normalized context
has the literal original initial edge, so it retains the original quotient
witness and nontrivial fixed-closure branch. The proved initial commutator
identity, which supplies source (1)–(3), bounds the endpoint commutator by
the original fixed subgroup. Inverse-conjugation covariance transports this
bound back to the actual edge family. The endpoint commutator containment
and the short distance to the original initial vertex give the other two
factors of the required intersection.

Source: the R2 paragraph after (9), printed p.40 / PDF p.30 of
`refs/files/stellmacher-n-group.pdf`. This module proves the upstream bound,
not the subsequent elimination of R2. The principal theorem retains the
parent's full family interface, although base value and covariance suffice
for this particular step.

The local API preserves all actual graph, quotient and configuration data.
Canonical statements remain exact wrappers, using fieldwise local data
conversion where required.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem adjacent_distance_bound
    {H : Type u} [Group H] [Finite H] {S P1 P2 : Subgroup H}
    (Γ : CosetGraphContext H S P1 P2) (left middle right : Γ.Vertex)
    (hadj : Γ.adjacent left middle) :
    Γ.distance left right ≤ Γ.distance middle right + 1 := by
  obtain ⟨path, hstart, hend, hpath⟩ := Γ.distance_path middle right
  let extended : Fin (Γ.distance middle right + 1 + 1) → Γ.Vertex :=
    Fin.cases left path
  have hextended : ∀ index : Fin (Γ.distance middle right + 1),
      Γ.adjacent (extended index.castSucc) (extended index.succ) := by
    intro index
    refine Fin.cases ?_ (fun offset => ?_) index
    · change Γ.adjacent left (path 0)
      rwa [hstart]
    · simpa [extended] using hpath offset
  simpa [extended, hend] using
    Γ.distance_le_of_path (Γ.distance middle right + 1) extended hextended

public theorem eight_four_shifted_geodesic_local
    {H : Type u} [Group H] [Finite H] {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (middle next : ctx.Γ.Vertex)
    (hfirst : ctx.Γ.adjacent ctx.criticalPath.a' middle)
    (hnext : ctx.Γ.adjacent middle next)
    (hlen : 2 < ctx.criticalPath.length)
    (hcomm : ⁅ZAt ctx.Γ next,
      ZAt ctx.Γ (ctx.criticalPath.path ⟨2, by omega⟩)⁆ ≠ ⊥) :
    let second := ctx.criticalPath.path ⟨2, by omega⟩
    IsCriticalPair ctx.Γ next second ∧
      ctx.Γ.distance next second = ctx.Γ.distance middle second + 1 ∧
      ZAt ctx.Γ second ≤ GAt ctx.Γ ctx.criticalPath.a := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : 2 < cp.length := hlen
  let second := cp.path ⟨2, by omega⟩
  change IsCriticalPair Γ next second ∧
    Γ.distance next second = Γ.distance middle second + 1 ∧
    ZAt Γ second ≤ GAt Γ cp.a
  have hend : Γ.distance cp.a' second ≤ cp.length - 2 := by
    have hbound := SevenSix.path_distance_le Γ cp 2 cp.length (by omega) le_rfl
    rw [cp.path_end, Γ.distance_symm] at hbound
    exact hbound
  have hmiddle := adjacent_distance_bound Γ middle cp.a' second (Γ.adjacent_symm hfirst)
  have hnextBound := adjacent_distance_bound Γ next middle second (Γ.adjacent_symm hnext)
  have hsecondAdj : Γ.adjacent cp.firstStep second := by
    have hedge := cp.path_adj ⟨1, by omega⟩
    change Γ.adjacent (cp.path ⟨1, by omega⟩) second at hedge
    rwa [cp.path_first] at hedge
  have hsecondCenter : ZAt Γ second ≤ Subgroup.centralizer (QAt Γ second : Set H) :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core second cp.firstStep
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hsecondAdj))).trans
        ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
          (SevenSix.centerAmbient_le_centralizer _))
  have hnot : ¬ ZAt Γ next ≤ QAt Γ second := by
    intro hcore
    apply hcomm
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hsecondCenter.trans (Subgroup.centralizer_le hcore))
  have hdist : Γ.distance next second = cp.length := by
    have hge : cp.length ≤ Γ.distance next second := by
      by_contra hbad
      exact hnot (SevenSix.critical_minimality Γ cp (by omega))
    omega
  have hcritical : IsCriticalPair Γ next second := by
    refine ⟨?_, hnot⟩
    rw [hdist, ← cp.endpoint_distance]
    exact cp.critical.1
  refine ⟨hcritical, by omega, ?_⟩
  have hstart : Γ.distance second cp.a ≤ 2 := by
    have hbound := SevenSix.path_distance_le Γ cp 0 2 (by omega) (by omega)
    change Γ.distance (cp.path 0) second ≤ 2 at hbound
    rw [cp.path_start, Γ.distance_symm] at hbound
    exact hbound
  have hcore : ZAt Γ second ≤ QAt Γ cp.a :=
    SevenSix.critical_minimality Γ cp (by omega)
  exact hcore.trans (by
    rw [show QAt Γ cp.a = twoCoreIn (GAt Γ cp.a) from Γ.twoCoreAt_def cp.a]
    exact Subgroup.map_subtype_le _)

public theorem eight_four_critical_commutator_le_edge_fixed_local
    {H : Type u} [Group H] [Finite H]
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
    (hcov : ∀ actor left right,
      F (ctx.Γ.act actor left) (ctx.Γ.act actor right) = (F left right).conjBy actor⁻¹)
    (left right neighbor : ctx.Γ.Vertex)
    (hcritical : IsCriticalPair ctx.Γ left right)
    (hcomm : ⁅ZAt ctx.Γ left, ZAt ctx.Γ right⁆ ≠ ⊥)
    (hadj : ctx.Γ.adjacent left neighbor)
    (hnear : ctx.Γ.distance left right = ctx.Γ.distance neighbor right + 1) :
    ⁅ZAt ctx.Γ left, ZAt ctx.Γ right⁆ ≤ F left neighbor := by
  let Γ := ctx.Γ
  let cp0 := ctx.criticalPath
  let h := ctx.sectionSeven
  obtain ⟨actor, cp, hleft, hright, hneighbor, hlen, horient⟩ :=
    exists_criticalPath_through_neighbor_with_orientation h Γ cp0
      left right neighbor hcritical hadj hnear
  have hcomm' : ⁅z Γ cp.a, z Γ cp.a'⁆ ≠ ⊥ := by
    rw [hleft, hright, z_act, z_act, ← Subgroup.map_commutator]
    intro hzero
    apply hcomm
    exact Subgroup.map_injective (MulAut.conj actor⁻¹).injective
      (hzero.trans (Subgroup.map_bot _).symm)
  have hcorrect : cp.a = cp0.a ∧ cp.firstStep = cp0.firstStep := by
    rcases horient with hgood | hbad
    · exact hgood
    · exfalso
      have hzcenter : z Γ cp.a ≤ CenterAmbient (stabilizer Γ cp.a) := by
        rw [hbad.1]
        exact hcenter
      apply hcomm'
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (hzcenter.trans ((SevenSix.centerAmbient_le_centralizer _).trans
          (Subgroup.centralizer_le (lemma_seven_four h Γ cp).reverse_containment.1)))
  rcases cp with ⟨start, terminal, length, hpos, hcrit, first, hedge, hdist,
    path, hstart, hend, hfirst, hpath, hSylow, hpair⟩
  dsimp only at hleft hright hneighbor hlen hcomm' hcorrect
  rcases hcorrect with ⟨hstart0, hfirst0⟩
  have hleft0 : cp0.a = Γ.act actor left := hstart0.symm.trans hleft
  have hneighbor0 : cp0.firstStep = Γ.act actor neighbor := hfirst0.symm.trans hneighbor
  have hpath0 : path 0 = cp0.a := hstart.trans hstart0
  have hpath1 : path ⟨1, by omega⟩ = cp0.firstStep := hfirst.trans hfirst0
  clear horient hleft hstart hneighbor hfirst
  subst start first
  let cp' : CriticalPath Γ := ⟨cp0.a, terminal, length, hpos, hcrit,
    cp0.firstStep, hedge, hdist, path, hpath0, hend, hpath1, hpath, hSylow, hpair⟩
  let ctx' : SectionEightLocalContext H S P1 P2 :=
    { sectionSeven := ctx.sectionSeven
      sixThree := ctx.sixThree
      Γ := Γ
      criticalPath := cp'
      commutator_ne := hcomm' }
  have hbound : ⁅z Γ cp0.a, z Γ terminal⁆ ≤ w.oneJFixedPoints S := by
    have hinitial := eight_four_initial_fixed_commutator_local ctx' hcenter w hbranch
    exact (Subgroup.commutator_mono le_rfl
      (opposite_center_le_opposite_closure_local ctx')).trans_eq hinitial
  have hmap : ⁅z Γ (Γ.act actor left), z Γ (Γ.act actor right)⁆ ≤
      F (Γ.act actor left) (Γ.act actor neighbor) := by
    rw [← hleft0, ← hright, ← hneighbor0, hbase]
    exact hbound
  rw [z_act, z_act, ← Subgroup.map_commutator, hcov] at hmap
  exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj actor⁻¹).injective).mp hmap

public theorem eight_four_shifted_commutator_bound_local
    {H : Type u} [Group H] [Finite H]
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
    (hlen : 2 < ctx.criticalPath.length) :
    let second := ctx.criticalPath.path ⟨2, by omega⟩
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    ⁅ZAt ctx.Γ second, ZAt ctx.Γ next⁆ ≤
      ZAt ctx.Γ second ⊓ (F next configuration.d ⊓ GAt ctx.Γ ctx.criticalPath.a) := by
  have _ := hsub
  have _ := hformula
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : 2 < cp.length := hlen
  let second := cp.path ⟨2, by omega⟩
  let next := Γ.act configuration.y⁻¹ cp.a'
  change ⁅ZAt Γ second, ZAt Γ next⁆ ≤ _
  by_cases hzero : ⁅ZAt Γ next, ZAt Γ second⁆ = ⊥
  · rw [Subgroup.commutator_comm, hzero]
    exact bot_le
  have hpos := cp.length_pos
  let previous := cp.path ⟨cp.length - 1, by omega⟩
  have hprevious : Γ.adjacent cp.a' previous := by
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
    rw [Γ.stabilizer_def] at hmem
    exact hmem
  have hmiddle : Γ.adjacent cp.a' configuration.d := by
    have hedge := adjacent_act Γ configuration.x⁻¹ hprevious
    rwa [hfix, ← configuration.hd] at hedge
  obtain ⟨hcritical, hnear, hsecond⟩ := eight_four_shifted_geodesic_local
    ctx configuration.d next hmiddle configuration.hadj hlen hzero
  have hfixed := eight_four_critical_commutator_le_edge_fixed_local ctx hcenter w hbranch
    F hbase hcov next second configuration.d hcritical hzero
    (Γ.adjacent_symm configuration.hadj) hnear
  have hcenters := critical_pair_commutator_le_inf
    (ctx.sectionSeven) Γ cp next second hcritical
  rw [Subgroup.commutator_comm]
  exact le_inf (hcenters.trans inf_le_right)
    (le_inf hfixed ((hcenters.trans inf_le_right).trans hsecond))

/-- Canonical specializations preserving the supplied graph, witness and family. -/
public theorem eight_four_critical_commutator_le_edge_fixed
    {H : Type u} [Group H] [Finite H]
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
    (hcov : ∀ actor left right,
      F (ctx.Γ.act actor left) (ctx.Γ.act actor right) = (F left right).conjBy actor⁻¹)
    (left right neighbor : ctx.Γ.Vertex)
    (hcritical : IsCriticalPair ctx.Γ left right)
    (hcomm : ⁅ZAt ctx.Γ left, ZAt ctx.Γ right⁆ ≠ ⊥)
    (hadj : ctx.Γ.adjacent left neighbor)
    (hnear : ctx.Γ.distance left right = ctx.Γ.distance neighbor right + 1) :
    ⁅ZAt ctx.Γ left, ZAt ctx.Γ right⁆ ≤ F left neighbor := by
  exact eight_four_critical_commutator_le_edge_fixed_local ctx.toLocalContext hcenter w hbranch F hbase hcov left right neighbor hcritical hcomm hadj hnear

public theorem eight_four_shifted_commutator_bound
    {H : Type u} [Group H] [Finite H]
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
    (hlen : 2 < ctx.criticalPath.length) :
    let second := ctx.criticalPath.path ⟨2, by omega⟩
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    ⁅ZAt ctx.Γ second, ZAt ctx.Γ next⁆ ≤
      ZAt ctx.Γ second ⊓ (F next configuration.d ⊓ GAt ctx.Γ ctx.criticalPath.a) := by
  exact eight_four_shifted_commutator_bound_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula configuration.toLocal hlen

end Stellmacher.SectionEight
