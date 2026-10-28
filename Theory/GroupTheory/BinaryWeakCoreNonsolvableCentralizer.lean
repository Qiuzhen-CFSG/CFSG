module

public import Theory.GroupTheory.BinaryWeakCoreCentralizerTransportReduction
public import Theory.GroupTheory.BinaryWeakCoreLocalStructure
public import Mathlib.GroupTheory.Solvable

/-!
# Nonsolvable-centralizer branch: normalized odd elements

The local isolated configuration has a quaternion centralizer inside the
chosen Sylow subgroup.  The transport reduction applies directly to an
ambient centralizer element once its conjugation preserves that local
centralizer.  The remaining GLS2 fusion argument is the separate input that
establishes this preservation for odd prime-power elements in the
nonsolvable branch.
-/

namespace Subgroup

/-- Transport for an odd prime-power element of a nonsolvable ambient
centralizer, assuming the local-centralizer normalization supplied by the
remaining fusion argument. -/
public theorem elementaryCommutingConnected_conj_of_nonsolvable_centralizer_of_local_normalization
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (_hG : ¬ Group.IsSolvable G) (S : Sylow 2 G) (A Q B E : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    [IsElementaryAbelian 2 E]
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B) (_hE : Nat.card E = 4)
    (hAS : A ≤ S) (hQS : Q ≤ S) (_hEQ : E ≤ Q)
    (hBweak : B ≤ Q ⊔ ((S : Subgroup G) ⊓ centralizer (Q : Set G)))
    (_hno : ¬ ∃ F : Subgroup G, IsElementaryAbelian 2 F ∧ Nat.card F = 4 ∧
      F ≤ Q ∧ Q ≤ normalizer (F : Set G))
    (_hiso : ∀ V : Subgroup G, IsElementaryAbelian 2 V → Nat.card V = 4 →
      V ≤ Q → ∀ W : Subgroup G, IsElementaryAbelian 2 W → Nat.card W = 4 →
      W ≤ S → W ≤ centralizer (V : Set G) → W = V)
    (_hunique : ∃! t : centralizer (Q : Set G), orderOf t = 2)
    (_hCns : ¬ Group.IsSolvable (centralizer (Q : Set G)))
    (p n : ℕ) (_hp : p.Prime) (_hp2 : p ≠ 2) (c : G)
    (hc : c ∈ centralizer (Q : Set G)) (_horder : orderOf c = p ^ n)
    (hcLocal : c ∈ normalizer (((S : Subgroup G) ⊓ centralizer (Q : Set G) : Subgroup G) : Set G)) :
    ElementaryCommutingConnected 2 A (A.map (MulAut.conj c).toMonoidHom) := by
  exact elementaryCommutingConnected_conj_of_normalizes_local_centralizer
    (S : Subgroup G) A Q B (S.isPGroup') hA hB hAS hQS hBweak c hc hcLocal

end Subgroup
