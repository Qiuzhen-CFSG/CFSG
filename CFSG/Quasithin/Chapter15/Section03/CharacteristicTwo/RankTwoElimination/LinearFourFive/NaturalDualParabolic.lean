module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Actions
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.ActionTransfer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.CenterObstruction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Selection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.MSData
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Preparation
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.ProjectedAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.NumericClassification

/-!
# The natural-plus-dual parabolic branch of 15.3.24

`false_of_source` excludes the actual natural-plus-dual module from the
permitted earlier source conclusions and the full C.1.34 witness. The span
splitting supplies the central supplement, and preparation constructs the
plane and inner Sylow action in the module's own quotient marking. The
projected-centre calculation then selects a point parabolic P over S∩L
with nontrivial O²(Y₊ ∩ P)-action.

At this same point, the literal input on O²(P)S retains the original Sylow
subgroup and the identity O²(P)S = PS. The earlier 15.3.11(12) implication
supplies MS3. Its commutator core has order at least 128 and center of order
at least sixteen, excluding C.1.34(1),(2),(3),(5); the original Sylow-center
bound excludes (4). The central supplement is retained throughout.

The legacy `MSData` and chief-factor APIs remain available, but their
stronger core equality is unnecessary for this contradiction. The earlier
source conclusions and universal classification remain explicit inputs for
the parent 15.3.24 assembly. Both choices of Hypothesis 15.3.10 are retained.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed pp.1129–1130 (PDF pp.1146–1147).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases

universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {d : LocalData G}
  {I : Subgroup G}

/-- The natural-plus-dual contradiction in 15.3.24, printed pp.1129–1130.
The plane, splitting, point action and literal MS input are constructed.
The explicit premises are the earlier source clauses: preparation uses
15.3.11–17; elementarity comes from 15.3.16(1); `hR`, `hspan`,
`hnormalizer` and `h11` retain 15.3.11(5i), 15.3.7, 15.3.11(3),(12);
the index and orders give the 15.3.8 obstruction. The full C.1.34 witness
is used at the ambient universe. Their final discharge belongs to the
owning 15.3.24 and Section 15.3 assemblies. -/
theorem false_of_source (c : ComponentWitness d I)
    [IsElementaryAbelian 2 (d.componentSpan c.L)]
    (classification : UniversalClassification.{u})
    (hI : I ∈ d.Hplus) (hf : CharacteristicTwo.HasCharacteristicTwo I)
    (hrank : primeRank 3 d.Yplus = 2) (earlier : Preparation.Earlier d c)
    (hq : IsSQTK κ I) (h : NaturalDual d c.L)
    (hR : d.R ≤ centralizer (d.V : Set G))
    (hspan : localSpan d.Z d.Y = d.V)
    (hnormalizer : OutsideStructure.SecondChoice d → normalizer (d.V₁ : Set G) ≤ d.M)
    (h11 : ∀ J : Subgroup G, J ≤ I →
      ⁅d.V, Stellmacher.twoResidualAmbient (d.Y ⊓ J)⁆ ≠ ⊥ → ¬ J ≤ d.M →
      ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
        ¬ ((C.map d.S.subtype).subgroupOf (J ⊔ d.S)).Normal)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (hZS : Nat.card d.ZS = 4) : False := by
  have hsplit := FourModules.centralSupplement_split_of_span_split
    (FourModules.naturalDual_span_split earlier.core_le_R hR h)
  obtain ⟨_, _, hi, p, _⟩ :=
    Preparation.source_preparation hI hf hrank earlier h.model
  obtain ⟨x, hx, hSP, hact⟩ :=
    Realization.ProjectedAction.exists_point c h p.marking earlier.yplus_le
      earlier.theta_local earlier.core_le_R hR hspan hsplit hnormalizer
  exact Realization.NumericClassification.false_of_inner classification h p.marking hx
    earlier.sylow earlier.component_eq_theta hi hSP hf hq hsplit hact h11 hindex hZ hZS

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic

end
