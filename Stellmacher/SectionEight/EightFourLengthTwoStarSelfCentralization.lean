module
public import Stellmacher.SectionEight.EightFourStarPredecessorModuleCentralization

/-!
# Transported stars centralize their modules at critical length two

Retain the actual local Section Eight context, central first-step center, faithful
fixed-center witness, nontrivial closure branch, and actual equivariant star
family with its neighbor-module containments. If the critical length is two,
every supplied conjugate of the first-step star centralizes the neighbor
module at that same vertex. The actor is explicit, so no assertion about
vertices outside the first-step orbit is needed.

At length two the path predecessor is exactly the first step. The proved
predecessor-module centralization therefore becomes self-centralization at
that vertex. The star and module covariance formulas transport the resulting
commutator equality by conjugation with the inverse actor, in the repository's
right-action convention. The canonical public theorem is retained as an
exact wrapper with the same supplied star family and actor.

This is the local commutator input for Stellmacher (8.4)(8), Journal of Algebra
190 (1997), p.39, refs/files/stellmacher-n-group.pdf. It supplies centralization
of each star with its own module; the commutation of different stars and the
exclusion of critical length two belong to the subsequent source-(8) argument.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

/-- At length two, the star at each supplied first-step conjugate centralizes its own module. -/
public theorem eight_four_length_two_star_centralizes_module_local
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
    (hCV : ∀ l, C l ≤ VAt ctx.Γ l)
    (hlen : ctx.criticalPath.length = 2) (g : H) :
    ⁅C (ctx.Γ.act g ctx.criticalPath.firstStep),
      VAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep)⁆ = ⊥ := by
  have hprev : ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,by omega⟩ =
      ctx.criticalPath.firstStep := by
    rw [← ctx.criticalPath.path_first]
    congr 1
    exact Fin.ext (by simp [hlen])
  have hbasecomm := eight_four_star_centralizes_predecessor_module_local
    ctx hcenter w hbranch C hC hbase (hCV ctx.criticalPath.firstStep)
  rw [hprev] at hbasecomm
  rw [hC]
  change ⁅(C ctx.criticalPath.firstStep).conjBy g⁻¹,
    v ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep)⁆ = ⊥
  rw [v_act]
  change ⁅(C ctx.criticalPath.firstStep).map (MulAut.conj g⁻¹).toMonoidHom,
    (VAt ctx.Γ ctx.criticalPath.firstStep).map (MulAut.conj g⁻¹).toMonoidHom⁆ = ⊥
  rw [← Subgroup.map_commutator,hbasecomm,Subgroup.map_bot]

/-- Canonical specialization retaining the same star family and actor. -/
public theorem eight_four_length_two_star_centralizes_module
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
    (hCV : ∀ l, C l ≤ VAt ctx.Γ l)
    (hlen : ctx.criticalPath.length = 2) (g : H) :
    ⁅C (ctx.Γ.act g ctx.criticalPath.firstStep),
      VAt ctx.Γ (ctx.Γ.act g ctx.criticalPath.firstStep)⁆ = ⊥ := by
  exact eight_four_length_two_star_centralizes_module_local ctx.toLocalContext
    hcenter w hbranch C hC hbase hCV hlen g
end Stellmacher.SectionEight
