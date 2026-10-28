module
public import Stellmacher.SectionEight.EightFourEndpointOppositeGeneration
public import Stellmacher.SectionEight.EightFourStarElementaryCore
public import Stellmacher.SectionEight.EightFourStarNeighborModule
public import Stellmacher.SectionEight.EightFourLengthTwoStarCommutation
public import Stellmacher.SectionEight.EightFourLengthTwoEndpointGeneration
public import Stellmacher.SectionEight.EightFourStarCentralizerTwoSubgroupCore
public import Stellmacher.SectionEight.EightFourLengthTwoFullCenterCommutator
/-!
# The actual neighboring-star configuration at critical length two

For the single transported edge-fixed family in the nontrivial-closure
branch of (8.4), critical length two supplies an endpoint actor whose
neighbor module together with the original first module contains the
endpoint residual. The same translated edge generates the endpoint
stabilizer together with the initial center. The star at that neighbor lies in the
original first-step core and commutes with the whole initial center modulo
the endpoint center.

All star covariance, normality, elementary/core and neighbor-module facts
come from the supplied F. The two residual-generating stars commute, and
Sylow conjugacy applies the actual star-centralizer core theorem to the
translated star inside the first stabilizer. Its core containment then
supplies the hypotheses of the full-center factor-commutator bound.
In particular, the endpoint core is not assumed contained in the original
edge Sylow; the two-subgroup form of the centralizer theorem is essential.

The proof uses the same local graph data for canonical and generated
contexts; the original canonical statements remain exact wrappers.

This assembles the proved first reductions of source (8) in Stellmacher
(8.4), Journal of Algebra 190 (1997), printed p.39. The final residual
contradiction requires further normalizer generation and is not asserted here.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_four_length_two_joint_configuration_local
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
    (hlen : ctx.criticalPath.length = 2)
 :
    let C l := ⨆ d, F d l
    ∃ g ∈ GAt ctx.Γ ctx.criticalPath.a',
      EAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep ⊔
        VAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep) ∧
      (ZAt ctx.Γ ctx.criticalPath.a ⊔
        (GAt ctx.Γ ctx.criticalPath.a' ⊓
          GAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep)) =
        GAt ctx.Γ ctx.criticalPath.a') ∧
      C (ctx.Γ.act g ctx.criticalPath.firstStep) ≤ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      ⁅C (ctx.Γ.act g ctx.criticalPath.firstStep),ZAt ctx.Γ ctx.criticalPath.a⁆ ≤
        ZAt ctx.Γ ctx.criticalPath.a' := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let C l := ⨆ d,F d l
  have hstar := eight_four_edge_star_closure_local ctx w F hbase hcov hsub hformula
  obtain ⟨hCbase,hCcov,hFC,hCn⟩ := hstar
  have hCV := eight_four_star_le_neighbor_module_local ctx w F hsub hformula
  have hCe := eight_four_star_elementary_core_local ctx hcenter w hbranch F hbase hcov hsub hformula
  obtain ⟨g,hg,hgen,hgenerate⟩ := eight_four_endpoint_opposite_generation_local ctx hlen
  refine ⟨g,hg,hgen,hgenerate,?_⟩
  have hcomm := eight_four_length_two_conjugate_stars_commute_local ctx hcenter w hbranch
    C hCcov hCbase hCV hCn hlen g hg hgen
  have hb : cp.length = 2 := hlen
  have hfirstend : Γ.adjacent cp.a' cp.firstStep := by
    have he := cp.path_adj ⟨1,by omega⟩
    have hi : (⟨1,by omega⟩ : Fin cp.length).succ =
        ⟨cp.length,Nat.lt_succ_self _⟩ := by apply Fin.ext; dsimp; omega
    rw [hi,cp.path_end] at he
    change Γ.adjacent (cp.path ⟨1,by omega⟩) cp.a' at he
    rw [cp.path_first] at he
    exact Γ.adjacent_symm he
  have hfix : Γ.act g cp.a' = cp.a' := by
    have heq : (stabilizer Γ cp.a' : Set H) = {x | Γ.act x cp.a' = cp.a'} := Γ.stabilizer_def _
    exact Set.ext_iff.mp heq g |>.mp hg
  have hCQ : C cp.firstStep ≤ q Γ cp.a' := by
    exact hCbase.le.trans (eight_four_fixed_closure_control_local ctx hcenter w hbranch).1
  have hCmQ : C (Γ.act g cp.firstStep) ≤ q Γ cp.a' := by
    have hh := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hCQ
    change (C cp.firstStep).conjBy g⁻¹ ≤ (q Γ cp.a').conjBy g⁻¹ at hh
    rw [← hCcov g cp.firstStep] at hh
    have hq := SevenSix.q_act Γ g cp.a'
    rw [hfix] at hq
    exact hh.trans_eq hq.symm
  have hQfirst : q Γ cp.a' ≤ stabilizer Γ cp.firstStep :=
    ((lemma_seven_three (ctx.sectionSeven) Γ).sylow_and_core
      cp.a' cp.firstStep ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hfirstend) default).2.2
  have hCcore : C (Γ.act g cp.firstStep) ≤ QAt Γ cp.firstStep := by
    apply eight_four_star_centralizer_two_subgroup_core_local ctx hcenter w hbranch _ (hCmQ.trans hQfirst)
    · let _ : IsElementaryAbelian 2 (C (Γ.act g cp.firstStep)) := (hCe _).1
      exact IsElementaryAbelian.isPGroup 2 _
    · have hh : ⁅C (Γ.act g cp.firstStep),C cp.firstStep⁆ = ⊥ := by
        rwa [Subgroup.commutator_comm]
      change ⁅C (Γ.act g cp.firstStep),(⨆ d,F d ctx.criticalPath.firstStep)⁆ = ⊥ at hh
      dsimp only at hCbase
      rwa [hCbase] at hh
  exact ⟨hCcore,eight_four_length_two_full_center_commutator_local ctx hcenter w hbranch
    C hCcov hCbase hCV hCn hlen g hg hgen hCcore⟩

public theorem eight_four_length_two_configuration_local
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
    (hlen : ctx.criticalPath.length = 2)
 :
    let C l := ⨆ d, F d l
    ∃ g ∈ GAt ctx.Γ ctx.criticalPath.a',
      EAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep ⊔
        VAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep) ∧
      C (ctx.Γ.act g ctx.criticalPath.firstStep) ≤ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      ⁅C (ctx.Γ.act g ctx.criticalPath.firstStep),ZAt ctx.Γ ctx.criticalPath.a⁆ ≤
        ZAt ctx.Γ ctx.criticalPath.a' := by
  obtain ⟨g, hg, hresidual, _hgenerate, hcore, hcomm⟩ :=
    eight_four_length_two_joint_configuration_local ctx hcenter w hbranch
      F hbase hcov hsub hformula hlen
  exact ⟨g, hg, hresidual, hcore, hcomm⟩

public theorem eight_four_length_two_joint_configuration
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
    (hlen : ctx.criticalPath.length = 2)
 :
    let C l := ⨆ d, F d l
    ∃ g ∈ GAt ctx.Γ ctx.criticalPath.a',
      EAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep ⊔
        VAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep) ∧
      (ZAt ctx.Γ ctx.criticalPath.a ⊔
        (GAt ctx.Γ ctx.criticalPath.a' ⊓
          GAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep)) =
        GAt ctx.Γ ctx.criticalPath.a') ∧
      C (ctx.Γ.act g ctx.criticalPath.firstStep) ≤ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      ⁅C (ctx.Γ.act g ctx.criticalPath.firstStep),ZAt ctx.Γ ctx.criticalPath.a⁆ ≤
        ZAt ctx.Γ ctx.criticalPath.a'  := by
  exact eight_four_length_two_joint_configuration_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula hlen

public theorem eight_four_length_two_configuration
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
    (hlen : ctx.criticalPath.length = 2)
 :
    let C l := ⨆ d, F d l
    ∃ g ∈ GAt ctx.Γ ctx.criticalPath.a',
      EAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep ⊔
        VAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep) ∧
      C (ctx.Γ.act g ctx.criticalPath.firstStep) ≤ QAt ctx.Γ ctx.criticalPath.firstStep ∧
      ⁅C (ctx.Γ.act g ctx.criticalPath.firstStep),ZAt ctx.Γ ctx.criticalPath.a⁆ ≤
        ZAt ctx.Γ ctx.criticalPath.a'  := by
  exact eight_four_length_two_configuration_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula hlen

end Stellmacher.SectionEight
