module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.Inputs
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.LinearThree
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.TerminalRank
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.AlphaAxis
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.PairedComponent
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.ComponentHall
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.HallTorus
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.OriginalAxes
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.BlockGeometry
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.BothBlocks
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.OppositeBorels
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.OvercomponentCentralizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.BorelNormalizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.CommonComponent
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.CoreQuotient
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.CoreCentrality
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.EvenDegree
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.CenterQuotient
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.OddCover
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.OddEmbedding
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.OddModels
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.OddRecognition

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.OriginalEmbedding
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalRow.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.ResidualPlacement
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.MovedComparison
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.RankTwoComparison
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.SingleFive
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.ActionPlacement

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.SmallAction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.Nonquasisimple
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.ThreePlacement

/-!
# The original moving-center Hall theorem and natural Hall placement

The marked natural row and both original natural blocks give the terminal
odd-rank contradiction whenever the Hall lies in the orbit Borel. The
comparison construction proves that containment for the rank-two cases.
Moved and single A₅ comparisons give the original Hall three-group bound
directly. The remaining small action images force the original comparison
quotient to be A₅, and A.3.6 plus Dickson's theorem do the same in the
nonquasisimple containing-component case. This completes the source Hall
contract with only its original authorized quotient-faithfulness premise.

Source 10.1.3 makes the original orbit index prime to three. Applying that
index theorem to the completed Hall bound gives literal Hall placement in
all natural cases, retaining both original quotient and Borel markings.
The earlier conditional APIs remain available with their unchanged types.
Source: Aschbacher–Smith 10.2.3, printed pp.745–747.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L C : Subgroup G}

/-- Apply the odd-rank calculation to the actual source Borel and axis. -/
theorem TerminalConfiguration.false {n : ℕ}
    (c : TerminalConfiguration T L C n) (hn : 1 < n) : False := by
  exact borel_normalizer_contradiction c.axis c.overcomponent
    ⁅ChapterB.baumann (T : Subgroup G), c.axis⁆ c.local_sqtk c.faithful
    c.centralizes hn c.axis_card c.model

end CFSG.Quasithin.Chapter10.MovingHall

namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 MovingHall
variable {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)

/-- Final assembly retains all three independent natural-branch obligations. -/
theorem source_nonnormalMovingHall_of_natural_branches
    (hrow : NaturalRowAt T) (hplace : NaturalHallPlacementAt T)
    (hterminal : NaturalTerminalAt T) : SourceNonnormalMovingHallAt T := by
  intro hmany L D hmin hn ha H hH hlarge hmove B hBM hHall hab hperm hfaith
  let c : MovingHall.Context D H B :=
    ⟨hmany,hmin,hn,ha,hH,hlarge,hmove,hBM,hHall,hab,hperm,hfaith⟩
  by_cases he : Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
  · exact linear_three_hall_isThreeGroup D hn hH hBM hHall hfaith he.some
  obtain ⟨n,hn,F,_,_,_,hF,e,hm⟩ := hrow L D H B c he
  have hB := hplace L D H B c n hn F hF e hm
  obtain ⟨terminal⟩ := hterminal L D H B c n hn F hF e hm hB
  exact (terminal.false hn).elim

/-- The common-component construction removes the terminal geometry premise.
This remains conditional on recognition, natural marking and Hall placement;
all three are retained by qt-d-10-nona5-moving-hall-three. -/
theorem source_nonnormalMovingHall_of_common_recognition
    (hrow : NaturalRowAt T) (hplace : NaturalHallPlacementAt T)
    (hrecognize : ∀ (L : Subgroup G)
      (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
      (H : Subgroup G) (B : Subgroup H), Context D H B →
      ∀ (n : ℕ), 1 < n → ∀ c : CommonOvercomponent T L H B n,
        Chapter1.Section02.LocalModels.IsSL c.overcomponent 3 (2^n) ∨
          ClassicalGroup.IsPSL c.overcomponent 3 (2^n)) :
    SourceNonnormalMovingHallAt T := by
  apply source_nonnormalMovingHall_of_natural_branches T hrow hplace
  intro L D H B ctx n hn F _ _ _ hF e mark hBB
  obtain ⟨c⟩ := ctx.common_overcomponent D n hn hF e mark hBB
  exact c.terminal (hrecognize L D H B ctx n hn c)


/-- The actual source construction discharges core separation, quotient
faithfulness and quasisimplicity before the remaining model recognition.
Natural marking, Hall placement and recognition remain owned by
qt-d-10-nona5-moving-hall-three. -/
theorem source_nonnormalMovingHall_of_faithful_common_recognition
    (hrow : NaturalRowAt T) (hplace : NaturalHallPlacementAt T)
    (hrecognize : ∀ (L : Subgroup G)
      (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
      (H : Subgroup G) (B : Subgroup H), Context D H B →
      ∀ (n : ℕ), 1 < n → ∀ c : CommonOvercomponent T L H B n,
        Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
          (inclusion c.original_lt.le)) →
        2*n ≤ primeRank 2 (c.overcomponent ⧸ pCore 2 c.overcomponent) →
        IsQuasisimple (c.overcomponent ⧸ pCore 2 c.overcomponent) →
        Chapter1.Section02.LocalModels.IsSL c.overcomponent 3 (2^n) ∨
          ClassicalGroup.IsPSL c.overcomponent 3 (2^n)) :
    SourceNonnormalMovingHallAt T := by
  apply source_nonnormalMovingHall_of_natural_branches T hrow hplace
  intro L D H B ctx n hn F _ _ _ hF e mark hBB
  obtain ⟨c,hi,hr,hq⟩ := ctx.common_overcomponent_faithful D n hn hF e mark hBB
  exact c.terminal (hrecognize L D H B ctx n hn c hi hr hq)

/-- The literal Hall consumer now needs recognition only in odd field degree,
with the actual common component already quasisimple. This task retains that
recognition and the natural-marking and Hall-placement obligations. -/
theorem source_nonnormalMovingHall_of_odd_quasisimple_recognition
    (hrow : NaturalRowAt T) (hplace : NaturalHallPlacementAt T)
    (hrecognize : ∀ (L : Subgroup G)
      (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
      (H : Subgroup G) (B : Subgroup H), Context D H B →
      ∀ (n : ℕ), 1 < n → Odd n → ∀ c : CommonOvercomponent T L H B n,
        Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
          (inclusion c.original_lt.le)) →
        2*n ≤ primeRank 2 (c.overcomponent ⧸ pCore 2 c.overcomponent) →
        IsQuasisimple c.overcomponent →
        Chapter1.Section02.LocalModels.IsSL c.overcomponent 3 (2^n) ∨
          ClassicalGroup.IsPSL c.overcomponent 3 (2^n)) :
    SourceNonnormalMovingHallAt T := by
  apply source_nonnormalMovingHall_of_natural_branches T hrow hplace
  intro L D H B ctx n hn F _ _ _ hF e mark hBB
  obtain ⟨c,hi,hr,_⟩ := ctx.common_overcomponent_faithful D n hn hF e mark hBB
  have ho : Odd n := Nat.not_even_iff_odd.mp (fun he => c.false_of_even_degree he hi)
  exact c.terminal (hrecognize L D H B ctx n hn ho c hi hr (c.quasisimple hi))

/-- Only projective recognition remains in the odd-degree terminal step.
Both literal block images and the quotient's genuine Theorem C catalogue
are proved inputs; the marked cover and actual two-core triviality are
then discharged. This owner retains projective recognition, natural-row
marking and Hall placement, so this is still conditional source assembly. -/
theorem source_nonnormalMovingHall_of_odd_projective_pair_recognition
    (hrow : NaturalRowAt T) (hplace : NaturalHallPlacementAt T)
    (hrecognize : ∀ (L : Subgroup G)
      (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
      (H : Subgroup G) (B : Subgroup H), Context D H B →
      ∀ (n : ℕ), 1 < n → Odd n → ∀ c : CommonOvercomponent T L H B n,
        Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
          (inclusion c.original_lt.le)) →
        2*n ≤ primeRank 2 (c.overcomponent ⧸ pCore 2 c.overcomponent) →
        IsQuasisimple c.overcomponent →
        IsSQTK KnownSimple.IsKnownSimple (c.overcomponent ⧸ center c.overcomponent) →
        Chapter1.Section02.LocalModels.TheoremCModel
          (c.overcomponent ⧸ center c.overcomponent) → CenterQuotientBlockPair c →
        ClassicalGroup.IsPSL (c.overcomponent ⧸ center c.overcomponent) 3 (2^n)) :
    SourceNonnormalMovingHallAt T := by
  apply source_nonnormalMovingHall_of_natural_branches T hrow hplace
  intro L D H B ctx n hn F _ _ _ hF e mark hBB
  obtain ⟨c,hi,hr,_⟩ := ctx.common_overcomponent_faithful D n hn hF e mark hBB
  have ho : Odd n := Nat.not_even_iff_odd.mp (fun he => c.false_of_even_degree he hi)
  obtain ⟨hsq,hm⟩ := c.center_quotient_catalogue hi
  exact (c.terminal_of_odd_center_quotient hn ho hi
    (hrecognize L D H B ctx n hn ho c hi hr (c.quasisimple hi) hsq hm
      (c.center_quotient_pair hi))).2.2

/-- The twenty-two embedding alternatives now reduce the actual odd-degree
source branch to its maximal rank-two parabolic row. The genuine A.3.12
embedding and identification of this row remain explicit local obligations,
along with natural marking and Hall placement; all are retained by
qt-d-10-nona5-moving-hall-three. -/
theorem source_nonnormalMovingHall_of_odd_parabolic_recognition
    (hrow : NaturalRowAt T) (hplace : NaturalHallPlacementAt T)
    (hrows : ∀ (L : Subgroup G)
      (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
      (H : Subgroup G) (B : Subgroup H), Context D H B →
      ∀ (n : ℕ), 1 < n → Odd n → ∀ c : CommonOvercomponent T L H B n,
        Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
          (inclusion c.original_lt.le)) →
        Chapter1.Section02.A312Conclusion
          ((c.original.subgroupOf c.overcomponent).map
            (QuotientGroup.mk' (center c.overcomponent))))
    (hrecognize : ∀ (L : Subgroup G)
      (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
      (H : Subgroup G) (B : Subgroup H), Context D H B →
      ∀ (n : ℕ), 1 < n → Odd n → ∀ c : CommonOvercomponent T L H B n,
        Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
          (inclusion c.original_lt.le)) →
        2*n ≤ primeRank 2 (c.overcomponent ⧸ pCore 2 c.overcomponent) →
        IsQuasisimple c.overcomponent →
        IsSQTK KnownSimple.IsKnownSimple (c.overcomponent ⧸ center c.overcomponent) →
        Chapter1.Section02.LocalModels.TheoremCModel
          (c.overcomponent ⧸ center c.overcomponent) → CenterQuotientBlockPair c →
        Chapter1.Section02.LocalModels.RankTwoTheoremC
          (⊤ : Subgroup (c.overcomponent ⧸ center c.overcomponent)) →
        Chapter1.Section02.IsParabolicResidual
          ((c.original.subgroupOf c.overcomponent).map
            (QuotientGroup.mk' (center c.overcomponent))) ⊤ true →
        ClassicalGroup.IsPSL (c.overcomponent ⧸ center c.overcomponent) 3 (2^n)) :
    SourceNonnormalMovingHallAt T := by
  apply source_nonnormalMovingHall_of_odd_projective_pair_recognition T hrow hplace
  intro L D H B ctx n hn ho c hi hr hq hsq hm hp
  obtain ⟨hRank,hPar⟩ := c.center_quotient_rank_two ho hi (hrows L D H B ctx n hn ho c hi)
  exact hrecognize L D H B ctx n hn ho c hi hr hq hsq hm hp hRank hPar

/-- In the literal odd-degree Hall branch only triality and Ree remain to
be excluded after the genuine embedding theorem. The field in the linear
case, the symplectic and G₂ exclusions, all small endpoints, and the lift
through the full central cover are discharged. The embedding, these last
two exclusions, natural marking and original Hall placement remain with
qt-d-10-nona5-moving-hall-three. -/
theorem source_nonnormalMovingHall_of_odd_triality_ree_exclusion
    (hrow : NaturalRowAt T) (hplace : NaturalHallPlacementAt T)
    (hrows : ∀ (L : Subgroup G)
      (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
      (H : Subgroup G) (B : Subgroup H), Context D H B →
      ∀ (n : ℕ), 1 < n → Odd n → ∀ c : CommonOvercomponent T L H B n,
        Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
          (inclusion c.original_lt.le)) →
        Chapter1.Section02.A312Conclusion
          ((c.original.subgroupOf c.overcomponent).map
            (QuotientGroup.mk' (center c.overcomponent))))
    (hexclude : ∀ (L : Subgroup G)
      (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
      (H : Subgroup G) (B : Subgroup H), Context D H B →
      ∀ (n : ℕ), 1 < n → Odd n → ∀ c : CommonOvercomponent T L H B n,
        Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
          (inclusion c.original_lt.le)) →
        2*n ≤ primeRank 2 (c.overcomponent ⧸ pCore 2 c.overcomponent) →
        IsQuasisimple c.overcomponent →
        IsSQTK KnownSimple.IsKnownSimple (c.overcomponent ⧸ center c.overcomponent) →
        Chapter1.Section02.LocalModels.TheoremCModel
          (c.overcomponent ⧸ center c.overcomponent) → CenterQuotientBlockPair c →
        Chapter1.Section02.IsParabolicResidual
          ((c.original.subgroupOf c.overcomponent).map
            (QuotientGroup.mk' (center c.overcomponent))) ⊤ true →
        ((∃ f : ℕ, 1 ≤ f ∧ Triality.Standard.IsTrialityGroupAt (2^f)
            (c.overcomponent ⧸ center c.overcomponent)) ∨
          (∃ m : ℕ, 1 ≤ m ∧ Chapter1.Section02.LocalModels.IsReeF4At
            (c.overcomponent ⧸ center c.overcomponent) m)) → False) :
    SourceNonnormalMovingHallAt T := by
  apply source_nonnormalMovingHall_of_odd_parabolic_recognition T hrow hplace hrows
  intro L D H B ctx n hn ho c hi hr hq hsq hm hp hRank hPar
  rcases c.center_quotient_rank_two_models ho hi hRank with hlinear | hexceptional
  · exact hlinear
  · exact (hexclude L D H B ctx n hn ho c hi hr hq hsq hm hp hPar hexceptional).elim

/-- The genuine A.3.12 embedding is the sole remaining terminal premise.
All model cases, the original-field identification, full central cover and
actual two-core triviality are discharged. This owner still retains the
embedding, natural-row marking and original Hall placement. -/
theorem source_nonnormalMovingHall_of_odd_embedding
    (hrow : NaturalRowAt T) (hplace : NaturalHallPlacementAt T)
    (hrows : ∀ (L : Subgroup G)
      (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
      (H : Subgroup G) (B : Subgroup H), Context D H B →
      ∀ (n : ℕ), 1 < n → Odd n → ∀ c : CommonOvercomponent T L H B n,
        Function.Injective ((QuotientGroup.mk' (pCore 2 c.overcomponent)).comp
          (inclusion c.original_lt.le)) →
        Chapter1.Section02.A312Conclusion
          ((c.original.subgroupOf c.overcomponent).map
            (QuotientGroup.mk' (center c.overcomponent)))) :
    SourceNonnormalMovingHallAt T := by
  apply source_nonnormalMovingHall_of_natural_branches T hrow hplace
  intro L D H B ctx n hn F _ _ _ hF e mark hBB
  obtain ⟨c,hi,_,_⟩ := ctx.common_overcomponent_faithful D n hn hF e mark hBB
  have ho : Odd n := Nat.not_even_iff_odd.mp (fun he => c.false_of_even_degree he hi)
  exact (c.terminal_of_odd_embedding hn ho hi (hrows L D H B ctx n hn ho c hi)).2.2

/-- Natural-row marking and the complete terminal geometry are discharged.
Only placement of the original Hall subgroup remains with this source owner. -/
theorem source_nonnormalMovingHall_of_hall_placement
    (hplace : NaturalHallPlacementAt T) : SourceNonnormalMovingHallAt T :=
  source_nonnormalMovingHall_of_natural_branches T source_natural_row hplace
    source_natural_terminal

/-- In the original moving branch, orbit containment suffices: the actual
Sylow normalizer and its two-residual Borel placement are proved. -/
theorem source_nonnormalMovingHall_of_hall_orbit
    (horbit : ∀ (L : Subgroup G)
      (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
      (H : Subgroup G) (B : Subgroup H), Context D H B →
      ∀ (n : ℕ), 1 < n →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 2^n →
      ∀ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F,
        NaturalMarking D e → B.map H.subtype ≤ localOrbit T L) :
    SourceNonnormalMovingHallAt T := by
  apply source_nonnormalMovingHall_of_hall_placement T
  intro L D H B ctx n hn F _ _ _ hF e mark
  exact MovingHall.HallPlacement.hall_le_borel_of_le_orbit D ctx e
    (horbit L D H B ctx n hn F hF e mark)

end CFSG.Quasithin.Chapter10


namespace CFSG.Quasithin.Chapter10
open Subgroup Theory.GroupTheory Chapter3.Section02 MovingHall
variable {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)

/-- Source p.746's Borel-normalization claim is the remaining geometric
input; the actual Hall placement, marked row and terminal contradiction
are supplied by the proved chain. -/
theorem source_nonnormalMovingHall_of_borel_normalizes_residual
    (hnorm : ∀ (L : Subgroup G)
      (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
      (H : Subgroup G) (B : Subgroup H), Context D H B →
      ∀ (n : ℕ), 1 < n →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 2^n →
      ∀ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F,
        NaturalMarking D e → sourceOrbitBorel T L ≤
          normalizer ((pResidual 2 H).map H.subtype : Set G)) :
    SourceNonnormalMovingHallAt T := by
  apply source_nonnormalMovingHall_of_hall_placement T
  intro L D H B ctx n hn F _ _ _ hF e mark
  exact MovingHall.HallPlacement.hall_le_borel_of_borel_normalizes_residual D ctx e
    (hnorm L D H B ctx n hn F hF e mark)

end CFSG.Quasithin.Chapter10

namespace CFSG.Quasithin.Chapter10
open Subgroup Theory.GroupTheory Chapter3.Section02 MovingHall MovingHall.HallPlacement
variable {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)

/-- The selected comparison, its common local overgroup, Borel normalization
of the containing component and the equality row are proved. Only proper
comparison embeddings retain a source geometric premise, owned here by
qt-d-10-nona5-moving-hall-three. -/
theorem source_nonnormalMovingHall_of_proper_comparison
    (hproper : ∀ (L : Subgroup G)
      (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
      (H : Subgroup G) (B : Subgroup H) (ctx : Context D H B),
      ∀ (n : ℕ), 1 < n →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 2^n →
      ∀ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F,
        NaturalMarking D e → ∀ c : ComparisonConfiguration D ctx,
        c.component.map H.subtype < c.overcomponent → sourceOrbitBorel T L ≤
          normalizer (c.component.map H.subtype : Set G)) :
    SourceNonnormalMovingHallAt T := by
  apply source_nonnormalMovingHall_of_hall_placement T
  intro L D H B ctx n hn F _ _ _ hF e mark
  exact hall_le_borel_of_proper_comparison D ctx n hn hF e mark
    (hproper L D H B ctx n hn F hF e mark)

end CFSG.Quasithin.Chapter10

namespace CFSG.Quasithin.Chapter10
open Subgroup Theory.GroupTheory Chapter3.Section02 MovingHall MovingHall.HallPlacement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type} [Field F] [Finite F] [CharP F 2]

/-- Every moved comparison component is now connected to the actual source
Hall conclusion. The A₅ case gives the bound directly; non-A₅ maximality
gives Hall placement and hence the checked terminal contradiction. -/
theorem source_natural_hall_three_of_moved_comparison
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (mark : NaturalMarking D e) (c : ComparisonConfiguration D ctx)
    (hne : c.component ≠ pResidual 2 H) : IsPGroup 3 B := by
  rcases c.hall_three_or_placed_of_moved D hne e with hthree | hplace
  · exact hthree
  · obtain ⟨terminal⟩ := source_natural_terminal L D H B ctx n hn F hF e mark hplace
    exact (terminal.false hn).elim

end CFSG.Quasithin.Chapter10

namespace CFSG.Quasithin.Chapter10
open Subgroup Theory.GroupTheory Chapter3.Section02 MovingHall MovingHall.HallPlacement
variable {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)

/-- All moved comparison components and the equal overcomponent row are
proved. Source assembly retains only the proper single-component embedding
K = O²(H) < I; its geometric normalization remains with this owner. -/
theorem source_nonnormalMovingHall_of_single_comparison
    (hsingle : ∀ (L : Subgroup G)
      (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
      (H : Subgroup G) (B : Subgroup H) (ctx : Context D H B),
      ∀ (n : ℕ), 1 < n →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 2^n →
      ∀ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F,
        NaturalMarking D e → ∀ c : ComparisonConfiguration D ctx,
        c.component = pResidual 2 H → c.component.map H.subtype < c.overcomponent →
        sourceOrbitBorel T L ≤ normalizer (c.component.map H.subtype : Set G)) :
    SourceNonnormalMovingHallAt T := by
  intro hmany L D hmin hn ha H hH hlarge hmove B hBM hHall hab hperm hfaith
  let ctx : Context D H B :=
    ⟨hmany,hmin,hn,ha,hH,hlarge,hmove,hBM,hHall,hab,hperm,hfaith⟩
  by_cases he : Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
  · exact linear_three_hall_isThreeGroup D hn hH hBM hHall hfaith he.some
  obtain ⟨n,hn,F,_,_,_,hF,e,mark⟩ := source_natural_row L D H B ctx he
  obtain ⟨c⟩ := exists_comparison_configuration D ctx n hn hF e mark
  by_cases hsingleK : c.component = pResidual 2 H
  · have hplace : B.map H.subtype ≤ sourceOrbitBorel T L := by
      by_cases heq : c.component.map H.subtype = c.overcomponent
      · exact c.hall_le_borel_of_eq D e heq
      · exact c.hall_le_borel_of_normalizes D e
          (hsingle L D H B ctx n hn F hF e mark c hsingleK (lt_of_le_of_ne c.component_le heq))
    obtain ⟨terminal⟩ := source_natural_terminal L D H B ctx n hn F hF e mark hplace
    exact (terminal.false hn).elim
  · exact source_natural_hall_three_of_moved_comparison D ctx n hn hF e mark c hsingleK

end CFSG.Quasithin.Chapter10

namespace CFSG.Quasithin.Chapter10
open Subgroup Theory.GroupTheory Chapter3.Section02 MovingHall MovingHall.HallPlacement
variable {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)

/-- All three rank-two single-comparison cases now give literal Hall placement.
The remaining proper single comparisons, including the source model sieve,
stay with this final assembly owner. No exceptional model is silently excluded. -/
theorem source_nonnormalMovingHall_of_single_remaining
    (hremaining : ∀ (L : Subgroup G)
      (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
      (H : Subgroup G) (B : Subgroup H) (ctx : Context D H B),
      ∀ (n : ℕ), 1 < n →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 2^n →
      ∀ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F,
        NaturalMarking D e → ∀ c : ComparisonConfiguration D ctx,
        c.component = pResidual 2 H → c.component.map H.subtype < c.overcomponent →
        ¬ ComparisonRankTwo (c.overcomponent ⧸ pCore 2 c.overcomponent) →
        sourceOrbitBorel T L ≤ normalizer (c.component.map H.subtype : Set G)) :
    SourceNonnormalMovingHallAt T := by
  apply source_nonnormalMovingHall_of_single_comparison T
  intro L D H B ctx n hn F _ _ _ hF e mark c hsingle hproper
  by_cases hm : ComparisonRankTwo (c.overcomponent ⧸ pCore 2 c.overcomponent)
  · exact c.borel_normalizes_of_single_rank_two D hsingle e hm
  · exact hremaining L D H B ctx n hn F hF e mark c hsingle hproper hm

end CFSG.Quasithin.Chapter10

namespace CFSG.Quasithin.Chapter10
open Subgroup Theory.GroupTheory Chapter3.Section02 MovingHall MovingHall.HallPlacement
variable {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)

/-- The direct A₅ bound removes that comparison from final source assembly,
including both its single and moved forms. The rank-two branch supplies literal
placement. Only proper non-A₅ single comparisons outside those models remain
with qt-d-10-nona5-moving-hall-three. -/
theorem source_nonnormalMovingHall_of_nonA5_single_remaining
    (hremaining : ∀ (L : Subgroup G)
      (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
      (H : Subgroup G) (B : Subgroup H) (ctx : Context D H B),
      ∀ (n : ℕ), 1 < n →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 2^n →
      ∀ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F,
        NaturalMarking D e → ∀ c : ComparisonConfiguration D ctx,
        c.component = pResidual 2 H → c.component.map H.subtype < c.overcomponent →
        ¬ Nonempty ((c.component ⧸ pCore 2 c.component) ≃* alternatingGroup (Fin 5)) →
        ¬ ComparisonRankTwo (c.overcomponent ⧸ pCore 2 c.overcomponent) →
        sourceOrbitBorel T L ≤ normalizer (c.component.map H.subtype : Set G)) :
    SourceNonnormalMovingHallAt T := by
  intro hmany L D hmin hn ha H hH hlarge hmove B hBM hHall hab hperm hfaith
  let ctx : Context D H B :=
    ⟨hmany,hmin,hn,ha,hH,hlarge,hmove,hBM,hHall,hab,hperm,hfaith⟩
  by_cases he : Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
  · exact linear_three_hall_isThreeGroup D hn hH hBM hHall hfaith he.some
  obtain ⟨n,hn,F,_,_,_,hF,e,mark⟩ := source_natural_row L D H B ctx he
  obtain ⟨c⟩ := exists_comparison_configuration D ctx n hn hF e mark
  by_cases hsingle : c.component = pResidual 2 H
  · by_cases hfive : Nonempty ((c.component ⧸ pCore 2 c.component) ≃* alternatingGroup (Fin 5))
    · exact c.hall_isThreeGroup_of_single_a5 D hsingle hfive.some
    have hplace : B.map H.subtype ≤ sourceOrbitBorel T L := by
      by_cases heq : c.component.map H.subtype = c.overcomponent
      · exact c.hall_le_borel_of_eq D e heq
      by_cases hmodel : ComparisonRankTwo (c.overcomponent ⧸ pCore 2 c.overcomponent)
      · exact c.hall_le_borel_of_single_rank_two D hsingle e hmodel
      exact c.hall_le_borel_of_normalizes D e
        (hremaining L D H B ctx n hn F hF e mark c hsingle
          (lt_of_le_of_ne c.component_le heq) hfive hmodel)
    obtain ⟨terminal⟩ := source_natural_terminal L D H B ctx n hn F hF e mark hplace
    exact (terminal.false hn).elim
  · exact source_natural_hall_three_of_moved_comparison D ctx n hn hF e mark c hsingle
end CFSG.Quasithin.Chapter10

namespace CFSG.Quasithin.Chapter10
open Subgroup Theory.GroupTheory Chapter3.Section02 MovingHall MovingHall.HallPlacement
open ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)

/-- The actual conjugation action removes every rank-two image, including
central covers of the recognized image. Equality, moved comparisons and the
single A₅ Hall bound are already discharged. The remaining small-action and
nonquasisimple-supplement normalization belongs to this same source owner,
qt-d-10-nona5-moving-hall-three. No point-control conclusion is assumed. -/
theorem source_nonnormalMovingHall_of_single_action_remaining
    (hremaining : ∀ (L : Subgroup G)
      (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
      (H : Subgroup G) (B : Subgroup H) (ctx : Context D H B),
      ∀ (n : ℕ), 1 < n →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 2^n →
      ∀ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F,
        NaturalMarking D e → ∀ c : ComparisonConfiguration D ctx,
        c.component = pResidual 2 H → c.component.map H.subtype < c.overcomponent →
        ¬ Nonempty ((c.component ⧸ pCore 2 c.component) ≃* alternatingGroup (Fin 5)) →
        ¬ ComparisonRankTwo (c.overcomponent ⧸ pCore 2 c.overcomponent) →
        letI := (c.orbit_reduced D).normal
        (¬ IsQuasisimple (c.overcomponent ⧸ pCore 2 c.overcomponent) ∨
          SmallComparisonAction
            ((c.overcomponent.subgroupOf (c.join D)).map (actionMk (c.orbit D)))) →
        sourceOrbitBorel T L ≤ normalizer (c.component.map H.subtype : Set G)) :
    SourceNonnormalMovingHallAt T := by
  intro hmany L D hmin hn ha H hH hlarge hmove B hBM hHall hab hperm hfaith
  let ctx : Context D H B :=
    ⟨hmany,hmin,hn,ha,hH,hlarge,hmove,hBM,hHall,hab,hperm,hfaith⟩
  by_cases he : Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
  · exact linear_three_hall_isThreeGroup D hn hH hBM hHall hfaith he.some
  obtain ⟨n,hn,F,_,_,_,hF,e,mark⟩ := source_natural_row L D H B ctx he
  obtain ⟨c⟩ := exists_comparison_configuration D ctx n hn hF e mark
  by_cases hsingle : c.component = pResidual 2 H
  · by_cases hfive : Nonempty ((c.component ⧸ pCore 2 c.component) ≃* alternatingGroup (Fin 5))
    · exact c.hall_isThreeGroup_of_single_a5 D hsingle hfive.some
    have hplace : B.map H.subtype ≤ sourceOrbitBorel T L := by
      by_cases heq : c.component.map H.subtype = c.overcomponent
      · exact c.hall_le_borel_of_eq D e heq
      by_cases hmodel : ComparisonRankTwo (c.overcomponent ⧸ pCore 2 c.overcomponent)
      · exact c.hall_le_borel_of_single_rank_two D hsingle e hmodel
      have hp := lt_of_le_of_ne c.component_le heq
      rcases c.single_hall_placement_or_remaining D hsingle hp n hn hF e with hplace | hrem
      · exact hplace
      · exact c.hall_le_borel_of_normalizes D e
          (hremaining L D H B ctx n hn F hF e mark c hsingle hp hfive hmodel hrem)
    obtain ⟨terminal⟩ := source_natural_terminal L D H B ctx n hn F hF e mark hplace
    exact (terminal.false hn).elim
  · exact source_natural_hall_three_of_moved_comparison D ctx n hn hF e mark c hsingle
end CFSG.Quasithin.Chapter10

namespace CFSG.Quasithin.Chapter10
open Subgroup Theory.GroupTheory Chapter3.Section02 MovingHall MovingHall.HallPlacement
variable {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)

/-- All three small-action carriers are discharged on the original comparison.
This reduction isolates the nonquasisimple containing two-core quotient. -/
theorem source_nonnormalMovingHall_of_nonquasisimple_comparison
    (hremaining : ∀ (L : Subgroup G)
      (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
      (H : Subgroup G) (B : Subgroup H) (ctx : Context D H B),
      ∀ (n : ℕ), 1 < n →
      ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 2^n →
      ∀ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F,
        NaturalMarking D e → ∀ c : ComparisonConfiguration D ctx,
        c.component = pResidual 2 H → c.component.map H.subtype < c.overcomponent →
        ¬ Nonempty ((c.component ⧸ pCore 2 c.component) ≃* alternatingGroup (Fin 5)) →
        ¬ ComparisonRankTwo (c.overcomponent ⧸ pCore 2 c.overcomponent) →
        ¬ IsQuasisimple (c.overcomponent ⧸ pCore 2 c.overcomponent) →
        sourceOrbitBorel T L ≤ normalizer (c.component.map H.subtype : Set G)) :
    SourceNonnormalMovingHallAt T := by
  apply source_nonnormalMovingHall_of_single_action_remaining T
  intro L D H B ctx n hn F _ _ _ hF e mark c hs hp hfive hm hrem
  by_cases hq : IsQuasisimple (c.overcomponent ⧸ pCore 2 c.overcomponent)
  · exact (hfive (c.single_a5_of_small_action D hs hq hp n hn hF e mark
      (hrem.resolve_left (not_not_intro hq)))).elim
  · exact hremaining L D H B ctx n hn F hF e mark c hs hp hfive hm hq

end CFSG.Quasithin.Chapter10

namespace CFSG.Quasithin.Chapter10
open Subgroup Theory.GroupTheory Chapter3.Section02 MovingHall MovingHall.HallPlacement
variable {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)

/-- The remaining nonquasisimple comparison also has an original A₅
quotient. The existing direct Hall bound closes this branch, leaving only
the original authorized faithfulness premise in the source contract. -/
theorem source_nonnormalMovingHall : SourceNonnormalMovingHallAt T := by
  apply source_nonnormalMovingHall_of_nonquasisimple_comparison T
  intro L D H B ctx n hn F _ _ _ hF e mark c hs _ hfive _ hq
  exact (hfive (c.single_a5_of_nonquasisimple D hs hq n hn hF e mark)).elim

/-- The literal Hall placement contract follows from the completed Hall
three-group bound and the original general-field component-index theorem. -/
theorem source_natural_hall_placement : NaturalHallPlacementAt T := by
  intro L D H B ctx _n _hn F _ _ _ _hF e _mark
  apply hall_le_borel_of_three D ctx e
  exact source_nonnormalMovingHall T ctx.many L D ctx.minimal ctx.nonnormal ctx.not_a5
    H ctx.hstar ctx.large ctx.moving B ctx.hall_le ctx.hall ctx.abelian ctx.permutes ctx.faithful

/-- The natural even-field row is impossible in the original moving-center
context. Its original Hall placement now discharges the terminal construction. -/
theorem source_natural_moving_false
    {L : Subgroup G} (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (mark : NaturalMarking D e) : False := by
  have hplace := source_natural_hall_placement T L D H B ctx n hn F hF e mark
  obtain ⟨terminal⟩ := source_natural_terminal L D H B ctx n hn F hF e mark hplace
  exact terminal.false hn

end CFSG.Quasithin.Chapter10
