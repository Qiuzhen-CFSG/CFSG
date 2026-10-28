module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal.Definitions
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal.Centralizer
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal.Terminal

/-!
# The diagonal endgame of Lemma 13.3.14

The inner quotient projection and the two-residual centralizer supplement
are constructed, and the final characteristic-two step is proved for the
literal J=KL₊T and W_K=[R₂(J),K]. The original noncontainment L₊≰K then
contradicts the core decomposition and commutator bound.

This is a conditional endgame, not the completed source implication.
The A.3.18 rank sieve, exclusion of L₃(2), actual A₅-module identification,
Baumann-normalizer escape, two-chief-factor count, and A₅-block/direct-factor
identification remain source obligations. In particular those conclusions
are not bundled into an asserted source setup or passed off as proved here.
The earlier reductions and all original L alternatives remain with the
whole-lemma assembly owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 13.3.14, printed p.893, PDF p.910.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The terminal application on the literal source carriers. The residual
supplement is constructed from the actual outer action, not assumed.
The remaining module, decomposition and chief-count conclusions are
explicit so their source producers and final discharge stay visible. -/
theorem contradiction_of_core_decomposition (K A T : Subgroup G)
    (hn : A ≤ normalizer K) (hK : IsPPerfect 2 K) (hA : IsPPerfect 2 A)
    (hc : center (K ⧸ pCore 2 K) = ⊥)
    (ho : IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K)))
    (hJ : localGroup K A T ∈ Chapter1.He G)
    (hout : ¬ A ≤ K)
    (hfix : centralizerResidual K A hn ≤ centralizer (movedModule K A T : Set G))
    (hsplit : ((localGroup K A T).pCoreIn 2 ⊓ centralizer (K : Set G)) ⊔
      movedModule K A T = (localGroup K A T).pCoreIn 2)
    (hdis : Disjoint ((localGroup K A T).pCoreIn 2 ⊓ centralizer (K : Set G))
      (movedModule K A T))
    (hm : ⁅(localGroup K A T).pCoreIn 2, A⁆ ≤ movedModule K A T) : False := by
  obtain ⟨_, hgen⟩ := exists_projection_and_residual_supplement K A hn hK hA hc ho
  apply hout
  apply le_component_of_core_decomposition (localGroup K A T) K A
    (centralizerResidual K A hn) (movedModule K A T) hJ
    (le_sup_right.trans le_sup_left)
    (((centralizerResidual_le K A hn).trans (quotientCentralizer_le K A hn)).trans
      le_sup_left) hn (centralizerResidual_twoPerfect K A hn) hgen hfix hsplit hdis hm

end CFSG.Quasithin.Chapter13.Section03.Noncentrality.Diagonal
