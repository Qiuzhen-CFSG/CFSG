module
public import Stellmacher.SectionNine.NineFourCentralStructure
public import Stellmacher.SectionNine.NineFourCentralFullFixedSubgroup
public import Stellmacher.SectionNine.NineFourCentralResidualNormalization
public import Stellmacher.SectionNine.NineFourCentralResidualContradiction

/-!
# Excluding the all-central auxiliary case of Stellmacher (9.4)

For the original normalized and enlarged counterexample, suppose every
literal auxiliary subgroup V_y is the next center. The counterexample
cannot exist. The supplied cardinal inequality is the independently proved
source-(4) reduction, and no action, fixed-subgroup identity, or residual
normalization conclusion is assumed.

The actual all-central structure theorem identifies the neighboring module
intersection with Z_a and makes A centralize the initial/remote core
intersection. The full fixed-subgroup comparison then gives
A=Z_a C_Vremote(Q_remote). Relative residual supplementation gives
[A V_next,E_next]≤V_next. The final residual-core contradiction applies
with Q=O₂(E_next), using the cyclic displacement index bound and residual
spanning to contradict source (4), or cubic containment to contradict
(7.6)(b).

This is the central paragraph from relation (7) to the end of Stellmacher
(9.4), printed pp.51–52 / PDF pp.41–42 of
`refs/files/stellmacher-n-group.pdf`. Together with the separate noncentral
branch it supplies the final numbered theorem.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_four_central_auxiliary_false
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A0 B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A0 B)
    (hb : 1 < ctx.criticalPath.length) (data : NineFourCounterexample ctx)
    (hremote : ctx.Γ.act data.conjugator data.remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : ctx.Γ.act data.conjugator data.remote ≠ ctx.criticalPath.firstStep)
    (henlarged : VAt ctx.Γ (ctx.Γ.act data.conjugator data.remote) ⊓
      VAt ctx.Γ ctx.criticalPath.firstStep ≤ data.subgroup)
    (hlarge : 4 * Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
      VAt ctx.Γ (ctx.Γ.act data.conjugator data.remote) : Subgroup G) ≤
        Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep))
    (hcentral : ∀ y ∈ data.subgroup,
      let F := (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ (ctx.Γ.act data.conjugator data.remote)) ⊔
        Subgroup.zpowers data.actor
      let Q := twoCoreIn (twoResidualIn F)
      (⁅Subgroup.zpowers y ⊔ VAt ctx.Γ ctx.criticalPath.firstStep,Q⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) = ZAt ctx.Γ ctx.criticalPath.firstStep) : False := by
  have hstructure := nine_four_central_structure ctx hb data hremote hne henlarged hlarge hcentral
  have hfixed := nine_four_central_full_fixed_subgroup ctx hb data hremote henlarged hstructure.2.1
  have hrescomm := nine_four_central_residual_normalization ctx hb data hremote hfixed.2
  exact nine_four_central_residual_contradiction ctx hb data hremote hne henlarged hlarge
    hstructure.1 hrescomm

end Stellmacher.SectionNine
