module

public import Stellmacher.SectionNine.DistanceOneFaithfulProducer
public import Stellmacher.SectionNine.DistanceOneCoreEquality
public import Stellmacher.SectionNine.DistanceOneLocalStructure
public import Stellmacher.SectionNine.DistanceOneNormalizerConstruction

/-!
# The distance-one commuting case

Stellmacher (9.1) describes the local quotients and two-cores when the critical
distance is one and the endpoint central subgroups commute. The first quotient
is the regular wreath product `SL₂(2) ≀ C₂`; the second is `SL₂(2)`. The
conclusion also retains the central product of two quaternion groups and an
order-eight subgroup whose normalizer in the ambient group has `L₃(2)` quotient.

Source: Stellmacher, Journal of Algebra 190 (1997), pp. 46–48, (9.1).
The wreath product is printed both in (a) and in proof relation (8); it is not
a semidirect product of a single `SL₂(2)` with `C₂`.

`DistanceOneReduction` separates the faithful-action, local-core, and ambient
normalizer-witness obligations and proves their conditional final assembly.
`DistanceOneNormalizerConstruction` now proves the ambient normalizer witness
from the explicit faithful and local conclusions. It selects the actual local
elementary eight, computes both S₄ normalizer quotients, and transfers the same
subgroup into the ambient group with self-centralization and distinct quotient
images. The numbered result below assembles the genuine faithful-action and
local-core producers with this witness construction.
-/

open scoped BigOperators Pointwise

namespace Stellmacher.SectionNine

open Stellmacher.Later
open Stellmacher.SectionsFiveToSeven

universe u

/-- The ambient-retaining form of Stellmacher (9.1). -/
public theorem lemma_nine_one_ambient
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) :
    let Vstar := conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a')
    QuotientIsModel
          (GAt ctx.Γ ctx.criticalPath.a)
          (QAt ctx.Γ ctx.criticalPath.a) SL2TwoWreathC2 ∧
      QuotientIsModel
          (GAt ctx.Γ ctx.criticalPath.a')
          (QAt ctx.Γ ctx.criticalPath.a') SL2Two ∧
      Nat.card S = 2 ^ 7 ∧
      QAt ctx.Γ ctx.criticalPath.a = ZAt ctx.Γ ctx.criticalPath.a ∧
      IsCentralProductQ8Q8 Vstar ∧
      ∃ U : Subgroup H,
        U ≤ Vstar.map embedding ∧ Nat.card U = 2 ^ 3 ∧
        QuotientIsModel (Subgroup.normalizer (U : Set H)) U L3Two := by
  have hfaith := distance_one_faithful_conclusion ctx hb
  have hcore := distance_one_core_eq_center_of_faithful ctx hb hfaith
  have hlocal := distance_one_local_conclusion_of_core_eq_center ctx hb hfaith hcore
  have hwitness := distance_one_normalizer_input_of_local_structure ctx hb hfaith hlocal
  exact distance_one_conclusion_of_data ctx hlocal hwitness

/-- **Stellmacher (9.1).**  In the case `b=1`, define
`V_{a'}^* = ⟨(Z_a ∩ Q_{a'})^{G_{a'}}⟩`; the three conclusions are recorded
with the source's wreath-product and central-product notation. -/
public theorem lemma_nine_one
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2)
    (hb : ctx.criticalPath.length = 1) :
    let Vstar := conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a')
    QuotientIsModel
          (GAt ctx.Γ ctx.criticalPath.a)
          (QAt ctx.Γ ctx.criticalPath.a) SL2TwoWreathC2 ∧
      QuotientIsModel
          (GAt ctx.Γ ctx.criticalPath.a')
          (QAt ctx.Γ ctx.criticalPath.a') SL2Two ∧
      Nat.card S = 2 ^ 7 ∧
      QAt ctx.Γ ctx.criticalPath.a = ZAt ctx.Γ ctx.criticalPath.a ∧
      IsCentralProductQ8Q8 Vstar ∧
      ∃ U : Subgroup H,
        U ≤ Vstar ∧ Nat.card U = 2 ^ 3 ∧
        QuotientIsModel (Subgroup.normalizer (U : Set H)) U L3Two := by
  simpa [SectionNineContext.toAmbientContext, SectionNineContext.toLocalContext,
    Subgroup.map_id] using
    lemma_nine_one_ambient ctx.toAmbientContext hb

end Stellmacher.SectionNine
