module
public import Stellmacher.SectionEight.EightFourConjugateStarCentralizerCore
public import Stellmacher.SectionEight.EightFourLengthTwoConfiguration
public import Stellmacher.SectionEight.EightFourLengthTwoResidualCentralization
public import Stellmacher.SectionEight.EightFourEdgeFixedTransport
/-!
# Critical length two is impossible in the nontrivial fixed-closure branch

For the centered-first-step local Section Eight context and its faithful
center witness, suppose the normal closure of the barred fixed subgroup is
larger than that subgroup. Then the critical path cannot have length two.
This proves source (8) in the proof of (8.4), without assuming a separately
chosen star family or the generation conclusions it needs.

Construct the actual equivariant edge-fixed family and its star closures.
The joint configuration provides one endpoint actor for both residual and
stabilizer generation. Its translated star centralizes the endpoint residual
core. That core is a two-subgroup of the translated neighbor stabilizer, so
the transported star-centralizer criterion puts it in the neighbor core.
The terminal version of (8.3), supplied by the proved same-graph ambient
callback, rules out exactly this containment. The original canonical API
is an exact wrapper through its local context adapter.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.4)(8), printed p.39,
`refs/files/stellmacher-n-group.pdf`. The longer-distance branch is separate.
-/
namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
public theorem eight_four_length_ne_two_of_nontrivial_closure_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : EightFourLocalContext H S P1 P2)
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
    : ctx.criticalPath.length ≠ 2 := by
  intro hlen
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  obtain ⟨F,hbase,hcov,hsub,hformula⟩ := eight_four_edge_fixed_transport_local ctx.toLocalContext hcenter w hbranch
  let C l := ⨆ d,F d l
  obtain ⟨hCbase,hCcov,_hFC,hCn⟩ := eight_four_edge_star_closure_local ctx.toLocalContext w F hbase hcov hsub hformula
  have hCV := eight_four_star_le_neighbor_module_local ctx.toLocalContext w F hsub hformula
  obtain ⟨g,hg,hres,hgen,hcore,_hcomm⟩ := eight_four_length_two_joint_configuration_local
    ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula hlen
  have hcentral := eight_four_length_two_residual_centralization_local ctx.toLocalContext hcenter w hbranch
    C hCcov hCbase hCV hCn hlen g hg hres hcore hgen
  let m := Γ.act g cp.firstStep
  have hadj : Γ.adjacent cp.a' cp.firstStep := by
    have he := cp.path_adj ⟨1,by change 1 < ctx.criticalPath.length; omega⟩
    have hi : (⟨1,by change 1 < ctx.criticalPath.length; omega⟩ : Fin cp.length).succ =
        ⟨cp.length,Nat.lt_succ_self _⟩ := by apply Fin.ext; simp; exact hlen.symm
    rw [hi,cp.path_end] at he
    change Γ.adjacent (cp.path ⟨1,by change 1 < ctx.criticalPath.length+1; omega⟩) cp.a' at he
    rw [cp.path_first] at he
    exact Γ.adjacent_symm he
  have hfix : Γ.act g cp.a' = cp.a' :=
    (Set.ext_iff.mp (Γ.stabilizer_def cp.a') g).mp hg
  have hadjm : Γ.adjacent cp.a' m := by
    have hh := adjacent_act Γ g hadj
    rwa [hfix] at hh
  have hn := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hadjm
  let Q := twoCoreIn (EAt Γ cp.a')
  have hQcore : Q ≤ q Γ cp.a' := by
    change twoCoreIn (EAt Γ cp.a') ≤ q Γ cp.a'
    rw [show EAt Γ cp.a' = twoResidualIn (GAt Γ cp.a') from Γ.twoResidualAt_def _]
    exact local_residual_core_le_vertex_core h Γ cp.a' m hn (GAt Γ cp.a') le_rfl
  have hQP : Q ≤ GAt Γ m := hQcore.trans
    ((lemma_seven_three h Γ).sylow_and_core cp.a' m hn default).2.2
  have hQtwo : IsPGroup 2 Q := (pCore_isPGroup (p := 2) (G := EAt Γ cp.a')).map _
  have hbound := eight_four_conjugate_star_centralizer_core_local ctx.toLocalContext hcenter w hbranch
    C hCbase hCcov g Q hQP hQtwo (by rwa [Subgroup.commutator_comm])
  exact eight_four_terminal_core_noncontainment_local ctx hcenter m hadjm hbound
public theorem eight_four_length_ne_two_of_nontrivial_closure
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
    : ctx.criticalPath.length ≠ 2  := by
  exact eight_four_length_ne_two_of_nontrivial_closure_local ctx.toEightFourContext hcenter w hbranch

end Stellmacher.SectionEight
