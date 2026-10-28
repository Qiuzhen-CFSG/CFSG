module

public import BenderSuzuki.ZD.Recognition
public import BenderSuzuki.ZD.Recognition.MinimalReduction.CoverReduction

/-!
# Theorem ZD from double-cover rigidity and residual embedding

The complete minimal-simple reduction is supplied by CoverReduction.
The proved strong-induction and Theorem SE assembly therefore leaves exactly
two independent source inputs: the double-cover Sylow-fixer theorem and the
residual strong-embedding argument for the resulting SimpleReduction.

Source: GLS, Volume 4, Chapter 2, Sections 3--4 and 5--17. Both remaining
source implications are explicit; this is not unconditional ZD recognition.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory
universe u

/-- The actual ZD consumer of the completed minimal-simple reduction.
No separate generation, radical, local-embedding or simplicity premise remains. -/
public theorem conclusion_of_doubleCoverRigidity_and_embedding
    (rigidity : DoubleCoverSylowRigidity.{u})
    (embed : ∀ {H : Type u} [Group H] [Finite H]
      (W : Set H) (N : Subgroup H),
      MinimalCounterexample W N → SimpleReduction W N → IsStronglyEmbedded N)
    {G : Type u} [Group G] [Finite G] (Z : Set G) (M : Subgroup G)
    (h : IsProductDisconnected Z M) : Conclusion Z M :=
  conclusion_of_simple_and_embedding_reductions
    (fun _ _ hm => hm.simpleReduction_of_doubleCoverRigidity rigidity) embed Z M h

end BenderSuzuki.ZD
