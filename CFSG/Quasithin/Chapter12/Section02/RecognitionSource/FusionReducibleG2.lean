module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleG2Model
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleG2Transport
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducible

/-!
# The G₂ row of the original 12.2.16 fusion argument

The given natural central quotient is a module for the actual derived G₂(2)
group. Irr⁺ generation makes V a quotient of its seven-dimensional Weyl
cover; the nonzero fixed space forces equality. The reconstructed action
therefore supplies the Sylow-central representatives needed by the fusion
argument. No action of full G₂(2), orbit assertion, or centralizer geometry
is assumed.

The only additional source premise is N_G(T) ≤ N_G(L). Its producer remains
with the original reducible-reduction owner. The final application below
removes the G₂ callback from `reducible_of_geometric_rows`.

Source: Aschbacher–Smith, 12.2.2(3f), p.795, and 12.2.16, pp.799–800.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08 ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The G₂ natural-quotient row gives global TI under the source Sylow
normalizer containment, with no further geometry or fusion input. -/
theorem globalTI_of_g2_row
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (e : ActionEquiv D.centralQuotientAction
      ((g2Natural (ZMod 2)).comp (commutator (Atlas.G2.Model (ZMod 2))).subtype)) :
    IsTISubgroup V := by
  obtain ⟨a,_,_⟩ := g2_weyl_model D hne e
  exact globalTI_of_g2_weyl_action h D structural hnone hNT a

/-- Actual application to the reducible assembly: the independent alternating
geometry is its only remaining row callback. -/
theorem reducible_of_alternating_geometric_row
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (rows : ModuleAlternatives1222 D)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (alternating : ∀ n : ℕ, 5 ≤ n → n ≤ 8 →
      (letI := D.actionCentralizer_normal
       ActionEquiv D.faithfulCentralAction (alternatingNatural n)) →
      IsTISubgroup V ∨ Nonempty (AlternatingEightFusionSeed T L V)) :
    IsTISubgroup V ∨ Nonempty (AlternatingEightFusion T L V) := by
  exact reducible_of_geometric_rows h D structural hnone rows hne alternating
    (globalTI_of_g2_row h D structural hnone hNT hne)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
