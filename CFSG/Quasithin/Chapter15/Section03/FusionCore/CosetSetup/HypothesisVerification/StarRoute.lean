module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.HypothesisVerification.Core
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.Basic

/-!
# A uniform normal-core argument from the earlier star calculation

The proof of 15.3.7, printed p.1122, establishes that Y* centralizes
C_M(V)* in M/O₂(M), using 14.1.17(3). The existing normal-closure lemma
propagates that earlier commutator bound from R_c to the actual residual Y.
Intersecting O₂(M) with Y gives [Y,C_M(V)] ≤ O₂(Y).

Consequently the normal-core residual X from 15.3.48 satisfies
[Y,X] ≤ O₂(Y) in both alternatives of 15.3.7. This treats both possibilities
for divisibility of |X| by three without any automorphism-order or theta
calculation. It uses the genuine earlier star bound, not an assumed bound
on X. The self-centralizing two-core of H supplies the local-overgroup
justification for the final uniqueness argument.

The extraspecial condition C_Y(V) ≤ H is still needed separately to place
L₁T in H; Layer.localL1_sup_le retains it. The full F.9.1 preamble and
the application of F.9.2 remain assembly obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.7, printed p.1122, and proof of 15.3.48, printed p.1142.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup
variable {G : Type*} [Group G] [Finite G]

/-- The earlier star bound gives a uniform commutator bound on C_M(V),
with Y the actual normal-closure residual. -/
theorem residualY_centralizer_commutator_le_core
    (M Mc V : Subgroup G) (hM : M ≤ normalizer (V : Set G))
    (hstar : ⁅(centralizer (V : Set G)).subgroupOf M,
      ((M ⊓ Mc).pCoreIn 2).subgroupOf M⁆ ≤ pCore 2 M) :
    ⁅residualY M Mc, M ⊓ centralizer (V : Set G)⁆ ≤ (residualY M Mc).pCoreIn 2 := by
  let C := (centralizer (V : Set G)).subgroupOf M
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    (hM.trans (normalizer_le_normalizer_centralizer _))
  have hc := residualY_commutator_le M Mc C (pCore 2 M) hstar
  have hm := map_mono (f := M.subtype) hc
  rw [map_commutator,
    map_subgroupOf_eq_of_le (Chapter14.SourcePreliminaries.sourceResidual_le M Mc)] at hm
  have hC : C.map M.subtype = M ⊓ centralizer (V : Set G) := by
    dsimp [C]
    rw [subgroupOf_map_subtype, inf_comm]
  rw [hC, commutator_comm] at hm
  have hY : M ≤ normalizer (residualY M Mc : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Chapter14.SourcePreliminaries.sourceResidual_le M Mc)).mp
      (residualY_normal M Mc)
  have hcY : ⁅residualY M Mc, M ⊓ centralizer (V : Set G)⁆ ≤ residualY M Mc :=
    le_normalizer_iff_commutator_le_left.mp (inf_le_left.trans hY)
  exact (le_inf hcY hm).trans
    (inf_pCoreIn_le_of_le 2 (Chapter14.SourcePreliminaries.sourceResidual_le M Mc))

/-- The complete normal-core calculation, uniformly in both branches of
15.3.7, from the genuine 14.1.17(3) input used in the proof of 15.3.7.
The residual-to-centralizer bound, its vanishing, and the relative core
containment are all conclusions. -/
theorem normal_core_of_source_star
    (M Mc H V A Z : Subgroup G) (T : Sylow 2 G) [(Z.subgroupOf H).Normal]
    (hAH : A ≤ H) (hZA : Z ≤ A) (hAM : normalizer (A : Set G) ≤ M)
    (hM : M ≤ normalizer (V : Set G)) (hTM : (T : Subgroup G) ≤ M)
    (hHZ : H ≤ centralizer (Z : Set G))
    (hfactor : ∀ x ∈ M ⊓ centralizer (Z : Set G),
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x)
    (hTH : (T : Subgroup G) ≤ H)
    (hchar : H ⊓ centralizer (H.pCoreIn 2 : Set G) ≤ H.pCoreIn 2)
    (hunique : Chapter4.UniqueMaximalOvergroup (residualY M Mc ⊔ (T : Subgroup G)) M)
    (houtside : ¬ H ≤ M)
    (hstar : ⁅(centralizer (V : Set G)).subgroupOf M,
      ((M ⊓ Mc).pCoreIn 2).subgroupOf M⁆ ≤ pCore 2 M) :
    centralizerCoreResidual H A Z ≤ M ⊓ centralizer (V : Set G) ∧
      centralizerCoreResidual H A Z = ⊥ ∧ centralizerCore H A Z ≤ pCore 2 H := by
  have hX := centralizerCoreResidual_le_centralizer M H V A Z T
    hAH hZA hAM hM hTM hHZ hfactor
  have hcomm : ⁅residualY M Mc, centralizerCoreResidual H A Z⁆ ≤
      (residualY M Mc).pCoreIn 2 :=
    (commutator_mono le_rfl hX).trans
      (residualY_centralizer_commutator_le_core M Mc V hM hstar)
  have hMY : M ≤ normalizer (residualY M Mc : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Chapter14.SourcePreliminaries.sourceResidual_le M Mc)).mp
      (residualY_normal M Mc)
  have hzero := centralizerCoreResidual_eq_bot_of_commutator M (residualY M Mc) H A Z T
    hTH (hTM.trans hMY) hchar hunique houtside (hcomm.trans le_sup_right)
  exact ⟨hX, hzero, centralizerCore_le_twoCore_of_residual_eq_bot H A Z hzero⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup

end
