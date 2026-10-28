module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowOmegaSpan

/-!
# The escaping omega action and the A₇ Sylow-normalizer consumer

The omega-span argument identifies the original chosen natural module with
the moved part of the actual L-span of Ω₁Z(T). Under normalizer escape its
cardinality bound and the two ambient residual identities eliminate C_Z(L).
The actual Z then has order four, and the nontrivial odd normalizer action
supplies the marked weight-two-to-weight-six transport in
`Points.transport_of_omegaSpan`.

Here that transport is applied to the literal `SylowNormalizer.no_transport`
obstruction, proving N(T) ≤ N(L). The final theorem discharges precisely this
premise of the existing Burnside--TI ambient fusion argument for 12.3.5.
No omega-cardinality, splitting, moving-element or fusion premise remains.

The local `Models` and `AmbientResiduals` inputs remain explicit as authorized
for this source branch. Their producers are the local-model and
ambient-residual branches; their final discharge belongs to the A₇
Sylow-normalizer assembly (`qt-d-1235-a7-sylow-normalizer`).

Source: Aschbacher--Smith, 3.3.6--8 and 3.3.22, printed pp.587--588 and
597--598, `refs/quasithin.pdf`; the fusion consumer is 12.3.5, printed p.809.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
variable {E : S.NaturalCoordinates}
namespace SylowNormalizer.Points
variable (P : Points E)

/-- The constructed marked transport contradicts the actual A₅-in-A₆
obstruction. Only the authorized earlier structural and residual inputs remain. -/
theorem normalizer_le_of_source_inputs
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (M : P.Models) (R : P.AmbientResiduals) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  by_contra hescape
  obtain ⟨g, hg, he⟩ := P.transport_of_omegaSpan structural M R hescape
  exact no_transport M R S.chosen.sylow_normalizes_component hg he

/-- Source 12.3.5 on the original chosen module, with its Sylow-normalizer
premise discharged by the actual omega action. -/
theorem controlsFusion_of_source_inputs
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (M : P.Models) (R : P.AmbientResiduals)
    (x y : G) (hx : x ∈ V) (hy : y ∈ V) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy : ∃ g : G, g * x * g⁻¹ = y) : ∃ l ∈ L, l * x * l⁻¹ = y :=
  E.controlsFusion structural (P.normalizer_le_of_source_inputs structural M R)
    x y hx hy hx1 hy1 hxy

end SylowNormalizer.Points
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
