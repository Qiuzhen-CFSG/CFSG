module
public import Stellmacher.SectionEight.EightFourEdgeStarClosure
public import Stellmacher.SectionThree.LemmaThreeSeven

/-!
# Nontrivial residual action on an overgroup of the fixed seed

In the strict fixed-center closure branch of (8.4), the first-step residual
cannot centralize any subgroup containing the original fixed seed. Otherwise
it normalizes the seed, as does the edge Sylow by the proved edge normality.
Residual-Sylow generation then makes the seed normal in the first-step
stabilizer, contradicting the strict closure branch.

In particular this supplies nontrivial residual action on the actual star.
No actor-index or fixed-space generation conclusion is assumed here.

The exact local context suffices for this argument. The original canonical
API is retained as a wrapper through the same graph and quotient witness.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

/-- Strict closure forces the first-step residual to act nontrivially on
every overgroup of the original fixed seed. -/
public theorem eight_four_fixed_overgroup_residual_action_nontrivial_local
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
    (C : Subgroup H) (hseedC : w.oneJFixedPoints S ≤ C) :
    ⁅twoResidualAmbient (GAt ctx.Γ ctx.criticalPath.firstStep), C⁆ ≠ ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let seed := w.oneJFixedPoints S
  let h := ctx.sectionSeven
  have hnormal := eight_four_edge_fixed_normal_local ctx hcenter w hbranch
  have hseedP : seed ≤ P := hnormal.1.trans inf_le_right
  intro hzero
  have hRF : twoResidualAmbient P ≤ Subgroup.normalizer (seed : Set H) :=
    ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hzero).trans
      (Subgroup.centralizer_le hseedC)).trans (Subgroup.centralizer_le_normalizer _)
  have hSF : S ≤ Subgroup.normalizer (seed : Set H) :=
    cp.S_le_edge_stabilizers.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hnormal.1).mp hnormal.2)
  have hlocal := (SevenSix.edge_local_data h Γ cp).2
  have hgen : twoResidualAmbient P ⊔ S = P :=
    SectionThree.twoResidual_sup_sylowImage hlocal.1.1.2.1.2
  have hPF : P ≤ Subgroup.normalizer (seed : Set H) := hgen ▸ sup_le hRF hSF
  let _ : (seed.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hseedP).mpr hPF
  apply hbranch
  change (Subgroup.normalClosure (seed.subgroupOf P : Set P)).map P.subtype = seed
  rw [Subgroup.normalClosure_eq_self, Subgroup.map_subgroupOf_eq_of_le hseedP]


/-- Canonical specialization with the same fixed seed and strict closure. -/
public theorem eight_four_fixed_overgroup_residual_action_nontrivial
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
    (C : Subgroup H) (hseedC : w.oneJFixedPoints S ≤ C) :
    ⁅twoResidualAmbient (GAt ctx.Γ ctx.criticalPath.firstStep), C⁆ ≠ ⊥ := by
  exact eight_four_fixed_overgroup_residual_action_nontrivial_local ctx.toLocalContext hcenter w hbranch C hseedC

end Stellmacher.SectionEight
