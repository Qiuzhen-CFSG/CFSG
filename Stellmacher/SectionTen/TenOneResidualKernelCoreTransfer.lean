module
public import Stellmacher.SectionTen.TenOneFirstCoreNoncontainment
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupTheory.SpecificGroups.PermThreeNormalKernel
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# Residual quotient action detects the first two-core

A two-subgroup of the first stabilizer in the actual Section Ten geometry
lies in its two-core if it centralizes the first residual two-core modulo
the first module. The first stabilizer quotient is assumed to be SL2(2).

The subgroup lies in the kernel of the actual conjugation action on the
residual core modulo its module intersection. If it escapes the two-core,
the S3 normal-kernel theorem forces a two-group action quotient. The entire
two-residual then lies in the kernel, contradicting its proved noncentral
action. This isolates the containment step preceding (8) in Stellmacher
(10.1)(a3), printed p.61, for the elementary centralizer Wstar; source:
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
open scoped commutatorElement
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

/-- The residual quotient action detects containment in the first two-core. -/
public theorem ten_one_two_subgroup_le_first_core_of_residual_commutator
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (D : Subgroup G) (hDP : D ≤ GAt ctx.Γ ctx.criticalPath.firstStep)
    (hDtwo : IsPGroup 2 D)
    (hcomm : ⁅D, twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)⁆ ≤
      VAt ctx.Γ ctx.criticalPath.firstStep) :
    D ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  classical
  let P := GAt ctx.Γ ctx.criticalPath.firstStep
  let Q := QAt ctx.Γ ctx.criticalPath.firstStep
  let E := EAt ctx.Γ ctx.criticalPath.firstStep
  let R := twoCoreIn E
  let V := VAt ctx.Γ ctx.criticalPath.firstStep
  have hE : E = twoResidualIn P := by
    change ctx.Γ.twoResidualAt ctx.criticalPath.firstStep = _
    rw [ctx.Γ.twoResidualAt_def]
    rfl
  have hEP : E ≤ P := hE ▸ twoResidualIn_le P
  have hRP : R ≤ P := (twoCoreIn_le E).trans hEP
  have hPR : P ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRP).mp
      (twoCoreIn_normal_of_normal E P hEP (hE ▸ twoResidualIn_normal P))
  have hPV : P ≤ Subgroup.normalizer (V : Set G) :=
    stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.firstStep
  have hN : (V.subgroupOf R).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hRP.trans hPV)
  let _ := hN
  obtain ⟨action, haction⟩ := Subgroup.exists_quotient_conjugation_action P R V hPR hPV hN
  by_contra hDnot
  have hDK : D.subgroupOf P ≤ action.ker :=
    Subgroup.quotient_conjugation_action_kills_commutator_layer P R V D hN hPR
      (Subgroup.commutator_comm D R ▸ hcomm) action haction
  have hQtwo : IsPGroup 2 (Q.subgroupOf P) := by
    have hQ : Q = twoCoreIn P := by
      change ctx.Γ.twoCoreAt ctx.criticalPath.firstStep = _
      rw [ctx.Γ.twoCoreAt_def]
      rfl
    rw [hQ, twoCoreIn, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      P.subtype_injective]
    exact pCore_isPGroup
  obtain ⟨projection, hsurj, hker⟩ := hmodel
  obtain ⟨equiv⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let f := equiv.toMonoidHom.comp projection
  have hquot : IsPGroup 2 (P ⧸ action.ker) :=
    Subgroup.quotient_isPGroup_two_of_perm_three_normal_kernel
      (Q.subgroupOf P) action.ker (D.subgroupOf P) hQtwo f
      (equiv.surjective.comp hsurj)
      (by dsimp only [f]; rw [MonoidHom.ker_comp_of_injective _ _ equiv.injective]; exact hker)
      (hDtwo.of_equiv (Subgroup.subgroupOfEquivOfLe hDP).symm) hDK (by
        intro hle
        apply hDnot
        intro element helement
        exact hle (show (⟨element, hDP helement⟩ : P) ∈ D.subgroupOf P from helement))
  have hres : twoResidualSubgroup P ≤ action.ker := by
    rw [SectionThree.twoResidualSubgroup_eq_hktPResidual']
    exact BenderSuzuki.External.hktPResidual_le action.ker inferInstance hquot
  have hEK : E ≤ action.ker.map P.subtype := by
    rw [hE, twoResidualIn, twoResidualAmbient]
    exact Subgroup.map_mono hres
  apply ten_one_first_core_action_not_le_module ctx middle hpath
  rw [Subgroup.commutator_comm]
  apply Subgroup.commutator_le.mpr
  intro actor hactor vector hvector
  obtain ⟨a, ha, rfl⟩ := hEK hactor
  let vectorR : R := ⟨vector, hvector⟩
  have hfix : action a (QuotientGroup.mk' (V.subgroupOf R) vectorR) =
      QuotientGroup.mk' (V.subgroupOf R) vectorR := by
    rw [show action a = 1 from ha]
    rfl
  rw [haction] at hfix
  have hmem := QuotientGroup.eq_iff_div_mem.mp hfix
  change (a : G) * vector * (a : G)⁻¹ / vector ∈ V at hmem
  change ⁅(a : G), vector⁆ ∈ V
  simpa only [commutatorElement_def, div_eq_mul_inv] using hmem
end Stellmacher.SectionTen
