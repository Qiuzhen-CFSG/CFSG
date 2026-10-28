module

public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.SylowKernelCore

/-!
# The reduced witness from the intrinsic module

For subnormal two-perfect X, the ambient two-core is a two-signalizer:
its commutator with X lies in the intrinsic core, which it contains.
A.4.8 therefore detects nontriviality of V(X) on Ω₁(Z(O₂(G))). The checked
minimal-witness theorem A.4.11 then makes [R₂(G),X] nontrivial.
Injective transport of the intrinsic module supplies the literal application
when X is viewed inside its original overgroup XT.
Source: Aschbacher--Smith, A.4.8(5), A.4.11, printed pp.59--61.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher

namespace CFSG.Quasithin.ChapterA.Section04
/-- The intrinsic module is preserved by an injective ambient homomorphism. -/
theorem intrinsicSignalizerModule_map_of_injective
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (X : Subgroup G) :
    intrinsicSignalizerModule (X.map f) = (intrinsicSignalizerModule X).map f := by
  change signalizerModule (X.map f) ((X.map f).pCoreIn 2) =
    (signalizerModule X (X.pCoreIn 2)).map f
  rw [signalizerModule_eq_commutator_omegaCenter, signalizerModule_eq_commutator_omegaCenter,
    ← map_pCoreIn_of_injective 2 X f hf, omegaOneCenterAmbient_map_injective f hf,
    map_commutator]

/-- Faithfulness of the intrinsic module supplies the movedness input to A.4.11. -/
theorem reduced_commutator_ne_bot_of_intrinsicModule_ne_bot
    {G : Type*} [Group G] [Finite G] (X : Subgroup G)
    (hsub : X.IsSubnormal) (hX : IsPPerfect 2 X)
    (hchief : HasCentralPChiefFactorsAbove 2 (pCore 2 X))
    (hne : intrinsicSignalizerModule X ≠ ⊥) :
    ⁅reducedTwoSubgroup G, X⁆ ≠ ⊥ := by
  have hn : X ≤ normalizer (pCore 2 G : Set G) := le_normalizer_of_normal
  have hc : ⁅X, pCore 2 G⁆ ≤ X.pCoreIn 2 := by
    rw [commutator_comm]
    exact (commutator_le_core_commutator_of_isSubnormal X (pCore 2 G)
      hsub hX pCore_isPGroup hn).trans (map_mono (commutator_le_left _ _))
  have hm := (signalizerModule_ne_bot_iff_intrinsic X (pCore 2 G) hX
    pCore_isPGroup hn (pCoreIn_le_of_subnormal 2 hsub) hc).mpr hne
  rw [signalizerModule_eq_commutator_omegaCenter, commutator_comm] at hm
  exact (reduced_witness_of_omegaCenter_moved X hsub hX hchief hm).2
end CFSG.Quasithin.ChapterA.Section04
