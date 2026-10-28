module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Inputs

/-!
# Assembly of the literal centralizer seed from the diagonal parabolic

The point stabilizer is constructed as C_{L₀T}(z). Its two-residual is the
original centralizer seed by the normal two-group quotient argument in
Preparation. The central involution supplies its nontrivial two-core.
Natural-action recognition and the intrinsic wreath residual calculation
then give all fields of the published seed contract, including relative
maximality and the actual quotient equivalence. The application supplies
every local embedding hypothesis for each overgroup of the literal XT.

The two independent calculations remain explicit inputs; this is not yet
an unconditional proof of ParabolicSeedAt.
Source: Aschbacher--Smith 10.2.4 and 10.2.11, pp.747,753--754, used in §10.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- Assemble the published source contract, retaining both outstanding calculations. -/
theorem parabolicSeed_of_recognition
    (hnatural : DiagonalRecognitionAt T) (hwreath : WreathResidualAt T) :
    ParabolicSeedAt T := by
  intro hmany L D s d
  obtain ⟨hmax,he⟩ := hnatural hmany L D s d
  have hTP := sylow_le_diagonalParabolic (L := L) d.central
  have hH := diagonalParabolic_mem_H (L := L) d.central d.order
  obtain ⟨hxi,hq⟩ := hwreath _ hTP hH he
  exact ⟨{
    parabolic := diagonalParabolic T L (d.first*d.second)
    sylow_le := hTP
    le_join := diagonalParabolic_le_join _
    maximal := hmax
    residual := diagonalParabolic_residual _
    xi := hxi
    quotient := hq
    wreath := he }⟩

/-- Actual application to the seed in each overgroup used by the closure proof. -/
theorem localInput_of_recognition
    (hnatural : DiagonalRecognitionAt T) (hwreath : WreathResidualAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) (d : CentralizerData T D s)
    {H : Subgroup G}
    (hH : centralizerSeed T L (d.first*d.second) ⊔ (T : Subgroup G) ≤ H) :
    ∃ P : Subgroup G,
      LocalInput 3 (T : Subgroup G) (centralizerSeed T L (d.first*d.second)) P H := by
  obtain ⟨r⟩ := parabolicSeed_of_recognition hnatural hwreath hmany L D s d
  exact r.localInput hH

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic
