module

public import Stellmacher.SectionNine.NineSevenCommutatorActionBridge

/-!
# Actual commutator centers in Stellmacher (9.7)

The actual terminal-module/initial-center commutator has order two and lies
in the second and penultimate path centers. This exports the action bridge
with the complete ambient hypothesis list required by the (9.7) geometry
assembly. Hypothesis Two remains on H and the embedding from G is retained.

The bridge proves the order using the actual involution conjugation action
on the elementary eight. Its normalized index-two neighbor-center argument
bounds the two relevant module/core commutators by their vertex centers.
No commutator order or center containment is assumed.

Source: Stellmacher, printed p.53 / PDF p.43 of
`refs/files/stellmacher-n-group.pdf`, proof of (9.7), from "Assume that
b > 3. Let R" through "With the same argument".
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem nine_seven_commutator_centers
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (third : ctx.Γ.Vertex)
    (_hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (_hindex : QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) 2)
    (hfirstCard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 2^3)
    (_hfirstModel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hendCard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^3)
    (_hendModel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2Two)
    (hstartData : ∀ vertex, IsConjugateVertex ctx.Γ ctx.criticalPath.a vertex →
      QuotientIsModel (GAt ctx.Γ vertex) (QAt ctx.Γ vertex) SL2Two ∧
        Nat.card (ZAt ctx.Γ vertex) = 4)
    (hlong : 3 < ctx.criticalPath.length) :
    let cp := ctx.criticalPath
    let R := ⁅VAt ctx.Γ cp.a', ZAt ctx.Γ cp.a⁆
    Nat.card R = 2 ∧
      R ≤ ZAt ctx.Γ (cp.path ⟨2, by dsimp [cp]; omega⟩) ∧
      R ≤ ZAt ctx.Γ (cp.path ⟨cp.length - 1, by dsimp [cp]; omega⟩) := by
  exact nine_seven_commutator_action_center_bridge ctx hb hfirstCard hendCard
    (fun vertex hvertex => (hstartData vertex hvertex).2)

end Stellmacher.SectionNine
