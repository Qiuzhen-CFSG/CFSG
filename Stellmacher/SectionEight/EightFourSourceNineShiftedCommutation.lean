module

public import Stellmacher.SectionEight.EightFourShiftedCommutatorElimination
public import Stellmacher.SectionEight.EightFourSourceNineIntersection
public import Stellmacher.SectionEight.EightFourShiftedCommutatorBound

/-!
# Shifted-center commutation for the source-nine witnesses

The second path center meets the selected intermediate center trivially,
using the actual first factor, actor and generating subgroup retained in the
source-nine configuration. This elimination is available on the actual local
context and local source-nine record; the canonical theorem is its exact
field-preserving wrapper. The proved shifted commutator bound and the exact
source-(9) intersection put R2 in this trivial intersection. Thus the second
path center commutes with the shifted terminal center, with the original
quotient witness, edge family and both extracted configurations unchanged.
Both steps hold over the exact local source-nine data. Their canonical
statements are preserved by fieldwise local-data wrappers.

Source: Stellmacher (8.4), R2 paragraph after (9), printed p.40 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_four_source_nine_second_center_inf_eq_bot_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (configuration : EightFourSourceNineLocalData ctx F)
    (hlen : 2 < ctx.criticalPath.length) :
    ZAt ctx.Γ (ctx.criticalPath.path ⟨2, by omega⟩) ⊓
      ZAt ctx.Γ configuration.d = ⊥ := by
  rw [configuration.hd]
  exact eight_four_first_configuration_second_center_inf_eq_bot_local
    ctx hcenter configuration.A configuration.L0 configuration.x
    configuration.hA configuration.hAprev configuration.hL0 configuration.hLgen
    configuration.hx configuration.hfirstfull hlen

public theorem eight_four_source_nine_second_center_inf_eq_bot
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (configuration : EightFourSourceNineData ctx F)
    (hlen : 2 < ctx.criticalPath.length) :
    ZAt ctx.Γ (ctx.criticalPath.path ⟨2, by omega⟩) ⊓
      ZAt ctx.Γ configuration.d = ⊥ :=
  eight_four_source_nine_second_center_inf_eq_bot_local ctx.toLocalContext
    hcenter F configuration.toLocal hlen

public theorem eight_four_source_nine_shifted_centers_commute_local
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
    ⁅ZAt ctx.Γ (ctx.criticalPath.path ⟨2, by omega⟩),
      ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a')⁆ = ⊥ := by
  have hbound := eight_four_shifted_commutator_bound_local ctx hcenter w hbranch
    F hbase hcov hsub hformula configuration hlen
  have hintersection := (eight_four_source_nine_intersection_local ctx hcenter w hbranch
    F hbase hcov hsub configuration).1
  dsimp only at hbound hintersection
  rw [hintersection,
    eight_four_source_nine_second_center_inf_eq_bot_local ctx hcenter F configuration hlen]
    at hbound
  exact bot_unique hbound


/-- Canonical specialization preserving the selected source-nine configuration. -/
public theorem eight_four_source_nine_shifted_centers_commute
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
    ⁅ZAt ctx.Γ (ctx.criticalPath.path ⟨2, by omega⟩),
      ZAt ctx.Γ (ctx.Γ.act configuration.y⁻¹ ctx.criticalPath.a')⁆ = ⊥ := by
  exact eight_four_source_nine_shifted_centers_commute_local ctx.toLocalContext hcenter w hbranch F hbase hcov hsub hformula configuration.toLocal hlen

end Stellmacher.SectionEight
