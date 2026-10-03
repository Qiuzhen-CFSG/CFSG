module
public import Stellmacher.SectionEight.EightFourLengthTwoStarSelfCentralization
public import Stellmacher.SectionEight.EightFourTerminalCoreResidualCentralizer
/-!
# Residual-generating conjugate stars commute at critical length two

At length two, suppose an endpoint stabilizer element transports the first
neighbor to another neighbor whose module, together with the first module,
contains the endpoint residual. Then the corresponding two actual stars
commute. The supplied generation is established separately from the local
factor decomposition; it is not inferred from the cardinality of a factor.
The local theorem retains the supplied graph, witness, stars and actor; its
canonical API is preserved as an exact local-context specialization.

Source (4) puts both stars in the endpoint core, which normalizes both stars
by their vertex normality. Their commutator therefore lies in each star.
Length-two star centrality makes it centralize both neighbor modules and
thus the residual they contain. The endpoint core has trivial residual
centralizer, so the commutator vanishes. This is the first calculation in
Stellmacher (8.4)(8), Journal of Algebra 190 (1997), printed p.39.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_four_length_two_conjugate_stars_commute_local
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
    (C : ctx.Γ.Vertex → Subgroup H)
    (hC : ∀ g d, C (ctx.Γ.act g d) = (C d).conjBy g⁻¹)
    (hbase : C ctx.criticalPath.firstStep = (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype)
    (hCV : ∀ d, C d ≤ VAt ctx.Γ d)
    (hCn : ∀ d, NormalIn (C d) (GAt ctx.Γ d))
    (hlen : ctx.criticalPath.length = 2) (g : H)
    (hg : g ∈ GAt ctx.Γ ctx.criticalPath.a')
    (hgen : EAt ctx.Γ ctx.criticalPath.a' ≤
      VAt ctx.Γ ctx.criticalPath.firstStep ⊔
        VAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep)) :
    ⁅C ctx.criticalPath.firstStep,C (ctx.Γ.act g ctx.criticalPath.firstStep)⁆ = ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  have hb : cp.length = 2 := hlen
  let m := Γ.act g cp.firstStep
  have hfirstend : Γ.adjacent cp.a' cp.firstStep := by
    have he := cp.path_adj ⟨1,by omega⟩
    have hi : (⟨1,by omega⟩ : Fin cp.length).succ =
        ⟨cp.length,Nat.lt_succ_self _⟩ := by apply Fin.ext; dsimp; omega
    rw [hi,cp.path_end] at he
    have hi0 : (⟨1,by omega⟩ : Fin cp.length).castSucc = ⟨1,by omega⟩ := rfl
    rw [hi0,cp.path_first] at he
    exact Γ.adjacent_symm he
  have hfix : Γ.act g cp.a' = cp.a' := by
    have heq : (stabilizer Γ cp.a' : Set H) = {x | Γ.act x cp.a' = cp.a'} := Γ.stabilizer_def _
    exact Set.ext_iff.mp heq g |>.mp hg
  have hm : Γ.adjacent cp.a' m := by
    have hh := adjacent_act Γ g hfirstend
    simpa only [hfix] using hh
  have hCQ : C cp.firstStep ≤ q Γ cp.a' := by
    rw [hbase]
    exact (eight_four_fixed_closure_control_local ctx hcenter w hbranch).1
  have hCmQ : C m ≤ q Γ cp.a' := by
    have hh := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hCQ
    change (C cp.firstStep).conjBy g⁻¹ ≤ (q Γ cp.a').conjBy g⁻¹ at hh
    rw [← hC g cp.firstStep] at hh
    have hq := SevenSix.q_act Γ g cp.a'
    rw [hfix] at hq
    exact hh.trans_eq hq.symm
  have hQfirst : q Γ cp.a' ≤ stabilizer Γ cp.firstStep :=
    ((lemma_seven_three h Γ).sylow_and_core cp.a' cp.firstStep
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hfirstend) default).2.2
  have hQm : q Γ cp.a' ≤ stabilizer Γ m :=
    ((lemma_seven_three h Γ).sylow_and_core cp.a' m
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hm) default).2.2
  have hNfirst : ⁅C cp.firstStep,C m⁆ ≤ C cp.firstStep :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hCmQ.trans (hQfirst.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (hCn cp.firstStep).1).mp (hCn cp.firstStep).2)))
  have hNm : ⁅C cp.firstStep,C m⁆ ≤ C m :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp
      (hCQ.trans (hQm.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (hCn m).1).mp (hCn m).2)))
  have hself : ⁅C cp.firstStep,VAt Γ cp.firstStep⁆ = ⊥ := by
    have hh := eight_four_length_two_star_centralizes_module_local ctx hcenter w hbranch C hC hbase hCV hlen 1
    simpa only [ctx.Γ.act_one] using hh
  have hselfm : ⁅C m,VAt Γ m⁆ = ⊥ :=
    eight_four_length_two_star_centralizes_module_local ctx hcenter w hbranch C hC hbase hCV hlen g
  have hNV : ⁅C cp.firstStep,C m⁆ ≤ Subgroup.centralizer
      ((VAt Γ cp.firstStep ⊔ VAt Γ m : Subgroup H) : Set H) := by
    apply Subgroup.le_centralizer_iff.mp
    apply sup_le
    · exact Subgroup.le_centralizer_iff.mpr
        (hNfirst.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hself))
    · exact Subgroup.le_centralizer_iff.mpr
        (hNm.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hselfm))
  apply le_bot_iff.mp
  rw [← eight_four_terminal_core_residual_centralizer_trivial_local ctx hcenter]
  exact le_inf (hNfirst.trans hCQ) (hNV.trans (Subgroup.centralizer_le hgen))

/-- Canonical specialization retaining the actual stars and residual generation. -/
public theorem eight_four_length_two_conjugate_stars_commute
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
    (C : ctx.Γ.Vertex → Subgroup H)
    (hC : ∀ g d, C (ctx.Γ.act g d) = (C d).conjBy g⁻¹)
    (hbase : C ctx.criticalPath.firstStep = (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype)
    (hCV : ∀ d, C d ≤ VAt ctx.Γ d)
    (hCn : ∀ d, NormalIn (C d) (GAt ctx.Γ d))
    (hlen : ctx.criticalPath.length = 2) (g : H)
    (hg : g ∈ GAt ctx.Γ ctx.criticalPath.a')
    (hgen : EAt ctx.Γ ctx.criticalPath.a' ≤
      VAt ctx.Γ ctx.criticalPath.firstStep ⊔
        VAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep)) :
    ⁅C ctx.criticalPath.firstStep,C (ctx.Γ.act g ctx.criticalPath.firstStep)⁆ = ⊥ := by
  exact eight_four_length_two_conjugate_stars_commute_local ctx.toLocalContext
    hcenter w hbranch C hC hbase hCV hCn hlen g hg hgen
end Stellmacher.SectionEight
