module
public import Stellmacher.SectionEight.EightFourStarCentralizerTwoSubgroupCore
/-!
# The star-centralizer core criterion at a translated neighbor

For any covariant star family whose first star is the actual nontrivial
closure, a two-subgroup of a translated neighbor stabilizer centralizing
that star lies in the translated neighbor core. Pull both subgroups back by
the same conjugator, use the proved first-star criterion, and map the core
containment forward through graph covariance. No new critical context or
choice of module action is introduced. The local theorem retains the actual
Section Eight graph, witness, family and conjugator. The canonical public
theorem is preserved as an exact specialization of this local result.

This is the last star-centralizer transfer in Stellmacher (8.4)(8),
Journal of Algebra 190 (1997), p.39, `refs/files/stellmacher-n-group.pdf`.
-/
namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
public theorem eight_four_conjugate_star_centralizer_core_local
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
    (hbase : C ctx.criticalPath.firstStep = (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype)
    (hcov : ∀ g l, C (ctx.Γ.act g l) = (C l).conjBy g⁻¹)
    (g : H) (D : Subgroup H)
    (hDP : D ≤ GAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep))
    (hD : IsPGroup 2 D)
    (hDC : ⁅D,C (ctx.Γ.act g ctx.criticalPath.firstStep)⁆ = ⊥) :
    D ≤ QAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep) := by
  let Γ := ctx.Γ
  let l := ctx.criticalPath.firstStep
  have hDP' : D.conjBy g ≤ GAt Γ l := by
    have h := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hDP
    change D.conjBy g ≤ (stabilizer Γ (Γ.act g l)).conjBy g at h
    rw [stabilizer_act,conjugateBy] at h
    change D.conjBy g ≤ ((GAt Γ l).conjBy g⁻¹).conjBy g at h
    rw [Subgroup.conjBy_inv'] at h
    exact h
  have hDC' : ⁅D.conjBy g,C l⁆ = ⊥ := by
    have h := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hDC
    rw [Subgroup.map_commutator,Subgroup.map_bot,hcov] at h
    change ⁅D.conjBy g,((C l).conjBy g⁻¹).conjBy g⁆ = ⊥ at h
    rwa [Subgroup.conjBy_inv'] at h
  have hbound := eight_four_star_centralizer_two_subgroup_core_local ctx hcenter w hbranch
    (D.conjBy g) hDP' (hD.map (MulAut.conj g).toMonoidHom) (hbase ▸ hDC')
  have h := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hbound
  change (D.conjBy g).conjBy g⁻¹ ≤ (QAt Γ l).conjBy g⁻¹ at h
  rw [Subgroup.conjBy_inv] at h
  change D ≤ q Γ (Γ.act g l)
  rw [SevenSix.q_act]
  exact h

/-- Canonical specialization with the same star family and conjugator. -/
public theorem eight_four_conjugate_star_centralizer_core
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
    (hbase : C ctx.criticalPath.firstStep = (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype)
    (hcov : ∀ g l, C (ctx.Γ.act g l) = (C l).conjBy g⁻¹)
    (g : H) (D : Subgroup H)
    (hDP : D ≤ GAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep))
    (hD : IsPGroup 2 D)
    (hDC : ⁅D,C (ctx.Γ.act g ctx.criticalPath.firstStep)⁆ = ⊥) :
    D ≤ QAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep) := by
  exact eight_four_conjugate_star_centralizer_core_local ctx.toLocalContext
    hcenter w hbranch C hbase hcov g D hDP hD hDC
end Stellmacher.SectionEight
