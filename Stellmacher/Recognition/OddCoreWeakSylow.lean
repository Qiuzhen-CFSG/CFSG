module
public import Stellmacher.Recognition.OddCoreSylow
public import Stellmacher.Recognition.BinaryWeakCoreFusion

/-!
# Odd-core control from binary weak-core fusion

Constancy of the involution odd-core closure on actual elementary commuting
components and naturality under conjugation turn component transport into
normalizer control. The Frattini reduction requires transport only for the
centralizer of Q. In particular, it proves weak-core control when Q contains
a normal elementary four-group, even if Q has elementary rank only two.

For a finite nonsolvable simple N₂ group, binary weak-core transport supplies
the general normalizer conclusion under the original weak-rank hypotheses.
This completes the application of the binary remark after GLS2, Proposition
22.4(i), `refs/KGroup/GLS2/ChapterF.tex`.
-/

namespace Stellmacher.Recognition

/-- Centralizer transport suffices for the full weak-core normalizer conclusion. -/
public theorem normalizer_le_normalizer_oddCoreClosure_of_centralizer_transport
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A Q B : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B)
    (hAS : A ≤ S) (hQS : Q ≤ S)
    (hBweak : B ≤ Q ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (Q : Set G)))
    (hC : ∀ c ∈ Subgroup.centralizer (Q : Set G),
      Subgroup.ElementaryCommutingConnected 2 A (A.map (MulAut.conj c).toMonoidHom)) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  intro g hg
  have htransport := Subgroup.elementaryCommutingConnected_conj_of_centralizer_transport
    (S : Subgroup G) A Q B S.isPGroup' hA hB hAS hQS
    (hBweak.trans (sup_le hQS inf_le_left))
    (hBweak.trans (sup_le_sup_left inf_le_right Q)) hC g hg
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change (involutionOddCoreClosure A).map (MulAut.conj g).toMonoidHom = _
  rw [involutionOddCoreClosure_map]
  exact (oddCoreClosure_eq_of_connected hN htransport).symm

/-- Weak-core normalizer control for a subgroup Q containing a normal four-group. -/
public theorem normalizer_le_normalizer_oddCoreClosure_of_weak_rank_of_normal_four
    {G : Type*} [Group G] [Finite G] (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A Q B E : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B] [IsElementaryAbelian 2 E]
    (hA : 8 ≤ Nat.card A) (hB : 8 ≤ Nat.card B) (hE : Nat.card E = 4)
    (hAS : A ≤ S) (hQS : Q ≤ S) (hEQ : E ≤ Q)
    (hQE : Q ≤ Subgroup.normalizer (E : Set G))
    (hBweak : B ≤ Q ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (Q : Set G))) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  intro g hg
  have htransport := Subgroup.elementaryCommutingConnected_conj_of_weak_rank_of_normal_four
    (S : Subgroup G) A Q B E S.isPGroup' hA hB hE hAS hQS hEQ hQE hBweak g hg
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change (involutionOddCoreClosure A).map (MulAut.conj g).toMonoidHom = _
  rw [involutionOddCoreClosure_map]
  exact (oddCoreClosure_eq_of_connected hN htransport).symm

/-- In a finite nonsolvable simple N₂ group, every weak-rank subgroup of S
has its normalizer in the normalizer of the rank-three odd-core closure. -/
public theorem normalizer_le_normalizer_oddCoreClosure_of_weak_rank
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A Q E B : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 B]
    (hAS : A ≤ S) (hA : 8 ≤ Nat.card A) (hQS : Q ≤ S)
    (hEQ : E ≤ Q) (hE : 4 ≤ Nat.card E)
    (hBQC : B ≤ Q ⊔ ((S : Subgroup G) ⊓ Subgroup.centralizer (Q : Set G)))
    (hB : 8 ≤ Nat.card B) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (involutionOddCoreClosure A : Set G) := by
  intro g hg
  have htransport := binaryWeakCore_transport hG hN S A Q E B
    hAS hA hQS hEQ hE hBQC hB g hg
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change (involutionOddCoreClosure A).map (MulAut.conj g).toMonoidHom = _
  rw [involutionOddCoreClosure_map]
  exact (oddCoreClosure_eq_of_connected hN htransport).symm

end Stellmacher.Recognition
