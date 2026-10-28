module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Recognition.Model.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Recognition

/-!
# The orbit-subspace route to the escaping displacement comparison

The finite representation argument is reduced to two independent statements.
First, either the escaping span is the entire module or the seed has index two
over the intersection of all its translates. Second, in this index-two case
the marked point stabilizer fixes the seed pointwise. The latter is stronger
than the supplied setwise invariance and still needs a proof.

`Basic` proves the actual local adjacency bound and the displacement transfer
from pointwise fixation. The assembly below applies this transfer to the
literal span-head action and the existing natural-section consumer. Its two
premises are left explicit: this module does not yet prove MS93 (1.6).

Source: Meierfrankenfeld--Stellmacher (1993), (1.6), pp.845--847;
the consumer is the inside-B branch of (4.4.1)(2), p.891.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
open Escape.Initial.Natural.Splitting

variable {E : Type*} [Group E] [IsElementaryAbelian 2 E]

/-- Assembly of the two orbit-subspace branches. The geometric dichotomy and
the pointwise fixation in its second branch are separate proof obligations. -/
theorem displacement_transfer_of_orbit_cases (ρ : SL →* MulAut E)
    (d : EscapingConfiguration ρ)
    (hcases : actionEscapingSpan ρ (markedPointStabilizer d.marking d.point)
      d.involution d.seed = ⊤ ∨ (actionOrbitCore ρ d.seed).relIndex d.seed = 2)
    (hstar : (actionOrbitCore ρ d.seed).relIndex d.seed = 2 →
      ∀ k ∈ markedPointStabilizer d.marking d.point, ∀ w ∈ d.seed, ρ k w = w) :
    actionDisplacement ρ (zpowers d.involution) ⊤ ≤
      actionDisplacement ρ (zpowers d.involution)
        (actionEscapingSpan ρ (markedPointStabilizer d.marking d.point)
          d.involution d.seed) := by
  rcases hcases with hwhole | hline
  · rw [hwhole]
  · exact displacement_transfer_of_seed_fixed ρ d (hstar hline)

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The two remaining finite-representation premises, applied to the literal
local quotient, give every clause of the existing marked natural section. -/
theorem hasNaturalSection_of_orbit_cases (source : LocalSource L R)
    (geometry : Geometry R) (hb : 4 < geometry.b R)
    {a c : Vertex R} (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (htriple : ⁅⁅localZSpan R a c, Q R c⁆, Ltilde R c⁆ ≤ Z R c)
    (hfaithful : Function.Injective (spanHeadAction source geometry a c hc))
    (d : EscapingConfiguration (spanHeadAction source geometry a c hc))
    (hcases : actionEscapingSpan (spanHeadAction source geometry a c hc)
      (markedPointStabilizer d.marking d.point) d.involution d.seed = ⊤ ∨
      (actionOrbitCore (spanHeadAction source geometry a c hc) d.seed).relIndex d.seed = 2)
    (hstar : (actionOrbitCore (spanHeadAction source geometry a c hc) d.seed).relIndex
      d.seed = 2 → ∀ k ∈ markedPointStabilizer d.marking d.point, ∀ w ∈ d.seed,
        spanHeadAction source geometry a c hc k w = w) : HasNaturalSection R a c := by
  let := spanHead_elementary geometry hb hc hd.le
  exact hasNaturalSection_of_escaping_transfer source geometry hb hc hd htriple hfaithful d
    (displacement_transfer_of_orbit_cases _ d hcases hstar)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
