module

public import Stellmacher.SectionEight.EightFourSourceNineConfiguration
public import Stellmacher.SectionEight.EightFourCentralVertexEdgeFixed
public import Stellmacher.SectionEight.EightFourTerminalNeighborCentral
public import Stellmacher.SectionEight.GeneratedContext

/-!
# The full intersection assertion in Stellmacher (8.4)(9)

For the original faithful witness, its transported edge-fixed family, and
the actual source-nine configuration, the selected edge-fixed subgroup meets
the initial stabilizer in exactly the selected intermediate vertex center.
The selected second endpoint center is not contained in that stabilizer.

The forward inclusion is retained in the configuration. Centrality at the
intermediate terminal neighbor puts its center in both incident edge-fixed
subgroups. The terminal center lies in the initial stabilizer by (7.4), giving
the reverse inclusion. If the second endpoint center were in that stabilizer,
its entire edge-fixed subgroup would equal the intermediate center. Edge
transitivity would then make the original fixed subgroup central, contradicting
the assumed strictness of its normal closure. The reversed edge orientation
is excluded by the original endpoint noncommutation.

Source: Stellmacher, Journal of Algebra 190 (1997), printed p.40, (8.4)(9),
`refs/files/stellmacher-n-group.pdf`. The later R2 and R1 arguments and the
final fixed-subgroup normality conclusion are not asserted here.

The local version retains the exact graph and all chosen subgroups; the
canonical theorem is an exact wrapper. The local data record retains the same
chosen configuration, and the canonical wrapper uses its fieldwise conversion.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

/-- A transported edge-fixed subgroup strictly contains the central second center
in the nontrivial original fixed-closure branch. -/
public theorem eight_four_edge_fixed_not_le_central_vertex_local
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
    (first second : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent first second)
    (hcentral : ZAt ctx.Γ second ≤ CenterAmbient (GAt ctx.Γ second)) :
    ¬ F first second ≤ ZAt ctx.Γ second := by
  intro hle
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  obtain ⟨actor, horient | horient⟩ :=
    (lemma_seven_one h Γ).edge_not_vertex_transitive.1 cp.firstStep_adj hadj
  · have hF := hcov actor cp.a cp.firstStep
    rw [horient.1, horient.2, hbase] at hF
    have hZ := z_act Γ actor cp.firstStep
    rw [horient.2] at hZ
    have hfixed : w.oneJFixedPoints S ≤ ZAt Γ cp.firstStep := by
      have hmap : (w.oneJFixedPoints S).conjBy actor⁻¹ ≤
          (ZAt Γ cp.firstStep).conjBy actor⁻¹ := by
        rw [← hF]
        change F first second ≤ (z Γ cp.firstStep).map (MulAut.conj actor⁻¹).toMonoidHom
        rw [← hZ]
        exact hle
      exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj actor⁻¹).injective).mp hmap
    let P := GAt Γ cp.firstStep
    have hFP : w.oneJFixedPoints S ≤ P :=
      hfixed.trans (hcenter.trans (Subgroup.map_subtype_le _))
    have hPF : P ≤ Subgroup.normalizer (w.oneJFixedPoints S : Set H) := by
      apply (Subgroup.centralizer_le_normalizer _).trans'
      apply Subgroup.le_centralizer_iff.mpr
      exact hfixed.trans (hcenter.trans (SevenSix.centerAmbient_le_centralizer P))
    let _ : ((w.oneJFixedPoints S).subgroupOf P).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hFP).mpr hPF
    apply hbranch
    change (Subgroup.normalClosure ((w.oneJFixedPoints S).subgroupOf P : Set P)).map
      P.subtype = w.oneJFixedPoints S
    rw [Subgroup.normalClosure_eq_self, Subgroup.map_subgroupOf_eq_of_le hFP]
  · have hZendP : z Γ (Γ.act actor cp.a') ≤ stabilizer Γ second := by
      rw [← horient.1, stabilizer_act, z_act]
      exact Subgroup.map_mono (lemma_seven_four h Γ cp).reverse_containment.1
    have hcomm : ⁅z Γ second, z Γ (Γ.act actor cp.a')⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (hcentral.trans ((SevenSix.centerAmbient_le_centralizer _).trans
          (Subgroup.centralizer_le hZendP)))
    rw [← horient.1, z_act, z_act, ← Subgroup.map_commutator] at hcomm
    exact ctx.commutator_ne (Subgroup.map_injective (MulAut.conj actor⁻¹).injective
      (hcomm.trans (Subgroup.map_bot _).symm))

/-- The original-context specialization of the local edge-fixed strictness result. -/
public theorem eight_four_edge_fixed_not_le_central_vertex
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
    (first second : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent first second)
    (hcentral : ZAt ctx.Γ second ≤ CenterAmbient (GAt ctx.Γ second)) :
    ¬ F first second ≤ ZAt ctx.Γ second :=
  eight_four_edge_fixed_not_le_central_vertex_local ctx.toLocalContext hcenter w hbranch
    F hbase hcov first second hadj hcentral

/-- Source (9), including the selected second endpoint's noncontainment in `G_a`. -/
public theorem eight_four_source_nine_intersection_local
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
    (configuration : EightFourSourceNineLocalData ctx F) :
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    F next configuration.d ⊓ GAt ctx.Γ ctx.criticalPath.a = ZAt ctx.Γ configuration.d ∧
      ¬ ZAt ctx.Γ next ≤ GAt ctx.Γ ctx.criticalPath.a := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  let previous := cp.path ⟨cp.length - 1, by omega⟩
  let next := Γ.act configuration.y⁻¹ cp.a'
  have hpos := cp.length_pos
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
  have hadj : Γ.adjacent cp.a' configuration.d := by
    have hedge := adjacent_act Γ configuration.x⁻¹ hprevious
    rwa [hfix, ← configuration.hd] at hedge
  have hcentral := eight_four_terminal_neighbor_central_local ctx hcenter configuration.d hadj
  have hreverse : ZAt Γ configuration.d ≤ F next configuration.d :=
    eight_four_central_vertex_le_edge_fixed_local ctx hcenter w F hbase hcov
      next configuration.d (Γ.adjacent_symm configuration.hadj) hcentral
  have hinitial : ZAt Γ configuration.d ≤ GAt Γ cp.a :=
    (eight_four_central_vertex_le_edge_fixed_local ctx hcenter w F hbase hcov
      cp.a' configuration.d hadj hcentral).trans
        (((hsub cp.a' configuration.d).trans inf_le_left).trans
          (lemma_seven_four h Γ cp).reverse_containment.1)
  have heq : F next configuration.d ⊓ GAt Γ cp.a = ZAt Γ configuration.d :=
    le_antisymm configuration.forward (le_inf hreverse hinitial)
  refine ⟨heq, ?_⟩
  intro hnext
  apply eight_four_edge_fixed_not_le_central_vertex_local ctx hcenter w hbranch F hbase hcov
    next configuration.d (Γ.adjacent_symm configuration.hadj) hcentral
  exact (le_inf le_rfl (((hsub next configuration.d).trans inf_le_left).trans hnext)).trans_eq heq


/-- Canonical specialization preserving all supplied local data. -/
public theorem eight_four_source_nine_intersection
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
    (configuration : EightFourSourceNineData ctx F) :
    let next := ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a'
    F next configuration.d ⊓ GAt ctx.Γ ctx.criticalPath.a = ZAt ctx.Γ configuration.d ∧
      ¬ ZAt ctx.Γ next ≤ GAt ctx.Γ ctx.criticalPath.a := by
  exact eight_four_source_nine_intersection_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub configuration.toLocal

end Stellmacher.SectionEight
