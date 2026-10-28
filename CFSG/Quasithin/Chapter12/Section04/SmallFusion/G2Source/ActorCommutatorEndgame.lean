module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.ActorOffenderCommutator
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.CommutatorEndgame

/-!
# The original G₂ commutator endgame from the full actor

The offender geometry of the full binary G₂ Weyl module supplies the literal
ambient commutator identity in the balanced-centralizer endgame. The action
image being an offender and the reciprocal centralizer indices remain inputs
of the independent local-group argument.

Source: Aschbacher--Smith 12.4.9, printed p.816, using B.4.6(3),(13).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 ChapterB.QuasisimpleSource Atlas.G2.Natural
local notation "F" => ZMod 2
local notation "E" => TraceZero F
local notation "σ" => traceZeroAction F
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The original 12.4.9 obstruction after transporting the offender commutator
calculation through the actual normalizer actor. -/
theorem lemma_12_4_9_of_offender_g2_actor
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : fixedSubgroup L V ≠ ⊥)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (b : V ≃* Multiplicative E)
    (φ : normalizer (L : Set G) →* Atlas.G2.Model F)
    (hφ : ∀ (m : normalizer (L : Set G)) (x : E),
      (b.symm (Multiplicative.ofAdd (σ (φ m) x)) : G) =
        (m : G) * (b.symm (Multiplicative.ofAdd x) : G) * (m : G)⁻¹)
    (g : G)
    (hAM : V.map (MulAut.conj g).toMonoidHom ≤ normalizer (L : Set G))
    (hoff : IsOffender σ (φ.comp (inclusion hAM)).range)
    (hindex : (centralizer (V.map (MulAut.conj g).toMonoidHom : Set G)).relIndex V =
      (centralizer (V : Set G)).relIndex (V.map (MulAut.conj g).toMonoidHom))
    (hcommne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  obtain ⟨_, _, _, _, hMV, _, _⟩ := exists_fixed_involution_setup h D structural e hne
  exact lemma_12_4_9_of_balanced_g2_commutator h D structural e hne hNT g hindex
    (actor_offender_commutator b φ hφ (hAM.trans hMV.le) hAM hoff) hcommne

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
