module

public import Theory.GroupTheory.PrimeRankNonabelianCube
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates.MatrixResults
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.LocalCertificates

/-!
# Odd local rank bounds in the concrete J₄ matrix group

The certified subgroups of orders 27 and 1331 are nonabelian: their
commutators are nonidentity by the injective three-local normal forms and
the eleven-local matrix relations. The prime-cube rank bound therefore
gives three-rank and eleven-rank at most two, respectively.

These results concern the actual ATLAS word subgroups. Their promotion to
Sylow subgroups of the ambient carrier is a separate obligation; no full
order or simplicity certification is used here.

Sources: GLS, *The Classification of the Finite Simple Groups*, Number 3,
Table 5.3i, printed p.270; ATLAS programs J4G1-max10W1 and J4G1-max7W1,
whose words and attribution are preserved in the imported local modules.
The consumer is Aschbacher–Smith, Theorem 0.1.2(5), printed p.4.
-/

private theorem nonabelian_of_commutator {G : Type*} [Group G]
    (H : Subgroup G) {x y z : G} (hx : x ∈ H) (hy : y ∈ H)
    (hz : x⁻¹ * y⁻¹ * x * y = z) (hz1 : z ≠ 1) : ¬ IsMulCommutative H := by
  intro hc
  have he := isMulCommutative_iff_of_setLike.mp hc x hx y hy
  apply hz1
  rw [← hz]
  simp [mul_assoc, he]

namespace Janko4.Simplicity

/-- Distinct normal forms certify a nonidentity commutator. -/
public theorem threeLocal_not_isMulCommutative
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    ¬ IsMulCommutative (threeLocalSubgroup hA hB) := by
  apply nonabelian_of_commutator (threeLocalSubgroup hA hB)
    (threeLocalU_mem hA hB) (threeLocalV_mem hA hB) rfl
  intro hz
  change threeLocalZ hA hB = 1 at hz
  have heq : threeLocalNormalForm hA hB (0, 0, 1) =
      threeLocalNormalForm hA hB (0, 0, 0) := by
    simp [threeLocalNormalForm, hz]
  have hfalse := threeLocalNormalForm_injective hA hB heq
  exact (by decide : ((0, 0, 1) : Fin 3 × Fin 3 × Fin 3) ≠ (0, 0, 0)) hfalse

/-- The concrete matrix relation certifies a nonidentity commutator. -/
public theorem Elevens.local_not_isMulCommutative
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    ¬ IsMulCommutative (Elevens.localSubgroup hA hB) := by
  exact nonabelian_of_commutator (Elevens.localSubgroup hA hB)
    (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    (Elevens.matrix_elevenRelations hA hB).commutator
    (Elevens.matrix_elevenRelations hA hB).z_ne

/-- The concrete order-27 subgroup has three-rank at most two. -/
public theorem threeLocal_primeRank_le_two
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    primeRank 3 (threeLocalSubgroup hA hB) ≤ 2 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact primeRank_le_two_of_nonabelian_card_cube
    (by simpa using threeLocal_card hA hB) (threeLocal_not_isMulCommutative hA hB)

/-- The concrete order-1331 subgroup has eleven-rank at most two. -/
public theorem Elevens.local_primeRank_le_two
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    primeRank 11 (Elevens.localSubgroup hA hB) ≤ 2 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  exact primeRank_le_two_of_nonabelian_card_cube
    (by simpa using Elevens.local_card hA hB) (Elevens.local_not_isMulCommutative hA hB)

end Janko4.Simplicity
