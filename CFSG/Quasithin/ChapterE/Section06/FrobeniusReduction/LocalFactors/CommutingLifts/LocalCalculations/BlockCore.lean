module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.LocalCalculations.Basic
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.Borel

/-!
# The two-core commutator calculation for an L₂-block

The actual quotient L/O₂(L) identifies the local Borel with the full
preimage of the triangular subgroup of SL₂(2^n). Restricting the quotient
map shows that this Borel has order 2^k(2^n−1). The supplied faithful cyclic
subgroup X has order 2^n−1, so its action detects the full odd part and
C_{L ∩ M}(V) lies in O₂(L ∩ M).

Odd actors with commuting action image normalize L ∩ M by the earlier
C-component theorem, and hence their commutators with X lie in that core.
The final theorem applies to arbitrary odd actors, including conjugate
cyclic candidates. The residual-lift specialization also allows actors
whose full order is not odd.

The Borel specification retains an actual quotient isomorphism. No new
block classification or cover identification is assumed or asserted here.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.11(3a)
and the proof of E.6.25, printed pp.249,255.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
variable {G : Type*} [Group G] [Finite G]

open Matrix Matrix.SpecialLinearGroup in
/-- The full Borel preimage has precisely the odd factor 2^n−1. -/
theorem l2_borel_card {L : Type*} [Group L] [Finite L] {B : Subgroup L} {n : ℕ}
    (hB : L2BlockBorel L B n) : ∃ k, Nat.card B = 2 ^ k * (2 ^ n - 1) := by
  obtain ⟨F, hfield, hfinite, hcard, e, hB⟩ := hB
  let := hfield
  let := hfinite
  let q : L →* SpecialLinearGroup (Fin 2) F :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = pCore 2 L := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective]
    exact QuotientGroup.eq_one_iff x
  let f := q.comp B.subtype
  have hfker : IsPGroup 2 f.ker := by
    change IsPGroup 2 (q.ker.comap B.subtype)
    rw [hqker]
    exact pCore_isPGroup.comap_subtype
  have hfrange : f.range = rankOneBorel F := by
    rw [MonoidHom.range_comp, range_subtype]
    rw [hB]
    exact map_comap_eq_self_of_surjective hq _
  obtain ⟨k, hk⟩ := hfker.exists_card_eq
  refine ⟨k + n, ?_⟩
  rw [← f.ker.card_mul_index, index_ker, hk, hfrange,
    L2Torus.card_borel, hcard, pow_add]
  ring

/-- The L₂-block model makes the local action kernel a two-group. -/
theorem l2Block_local_kernel_le_core {K : GroupClass} {T : Sylow 2 G}
    {M V U X L : Subgroup G}
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hX : RegularCyclicSection M V U X)
    (hL : L ≤ centralizer (U : Set G)) (hXL : X ≤ L)
    (hB : L2BlockBorel L ((L ⊓ M).subgroupOf L) (subgroupCorank V U)) :
    (L ⊓ M) ⊓ centralizer (V : Set G) ≤ (L ⊓ M).pCoreIn 2 := by
  obtain ⟨k, hk⟩ := l2_borel_card hB
  have hcard : Nat.card (L ⊓ M : Subgroup G) = 2 ^ k * Nat.card X := by
    rw [hX.card_eq]
    simpa only [Nat.card_congr (subgroupOfEquivOfLe
      (inf_le_left : L ⊓ M ≤ L)).toEquiv] using hk
  exact local_kernel_le_core_of_card
    ((le_inf inf_le_right (inf_le_left.trans hL)).trans
      (h.localCentralizer_le_normalizer hU.2.1 hU.1))
    (le_inf hXL (hX.contained.trans (inf_le_left.trans inf_le_left))) hX.faithful hcard

/-- The distinguished block calculation for each nondistinguished residual lift. -/
theorem residualLift_commutator_le_core_l2Block {K : GroupClass} {T : Sylow 2 G}
    {M V U X L : Subgroup G} [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (D : Representation.RegularCyclicNormalClosure.Decomposition
      (automizerRepresentation V) (inducedAutomizer V X))
    (i : Fin D.size) (hi : i ≠ D.distinguished)
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G))) (hXL : X ≤ L)
    (hB : L2BlockBorel L ((L ⊓ M).subgroupOf L) (subgroupCorank V U)) :
    ⁅residualLift V (D.factor i), X⁆ ≤ (L ⊓ M).pCoreIn 2 :=
  (residualLift_commutator_le_local_kernel h earlier hU hX D i hi hL hXL).trans
    (l2Block_local_kernel_le_core h hU hX hL.1 hXL hB)

/-- The full local calculation for the L₂-block branch, for every odd actor
with commuting action image. The two-core bound is proved from the actual
Borel quotient, rather than assumed of its centralizer. -/
theorem odd_commutator_le_core_l2Block {K : GroupClass} {T : Sylow 2 G}
    {M V U X L A : Subgroup G} [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V) (earlier : EarlierResidualNormalization K)
    (hU : U ∈ obstructionFamily M V) (hX : RegularCyclicSection M V U X)
    (hL : L ∈ Chapter1.cComponentsIn (centralizer (U : Set G))) (hXL : X ≤ L)
    (hB : L2BlockBorel L ((L ⊓ M).subgroupOf L) (subgroupCorank V U))
    (hA : A ≤ normalizer (V : Set G)) (ho : Odd (Nat.card A))
    (hc : ∀ a ∈ inducedAutomizer V A, ∀ x ∈ inducedAutomizer V X, Commute a x) :
    ⁅A, X⁆ ≤ (L ⊓ M).pCoreIn 2 := by
  have hXB : X ≤ L ⊓ M := le_inf hXL
    (hX.contained.trans (inf_le_left.trans inf_le_left))
  have hn := odd_normalizes_local_intersection h earlier hU hX hL hA ho hc
  have hcomm : ⁅A, X⁆ ≤ L ⊓ M :=
    (commutator_mono le_rfl hXB).trans (le_normalizer_iff_commutator_le_right.mp hn)
  exact (le_inf hcomm (cross_commutator_le_kernel hA
    (hX.contained.trans (inf_le_left.trans inf_le_right)) hc)).trans
      (l2Block_local_kernel_le_core h hU hX hL.1 hXL hB)

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
