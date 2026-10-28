module

public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.MatrixModel
public import Theory.GroupTheory.PrimeRankWitness

/-!
# Defining-characteristic rank in PSL₃

The first root plane of the existing concrete unitriangular matrix model
embeds F² in PSL₃(F). The embedding is valid in every characteristic,
despite the historical `PSL3Even` namespace. Thus |F| = p^e gives rank
at least 2e; in particular the ordinary rank is at least four when e = 2.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, A.2.17, printed p.39. This distinguishes the defining rank from
the nondefining ranks used in the central-cover argument.
-/

@[expose] public section

open Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.DefiningRank
variable (F : Type*) [Field F]

theorem two_mul_fieldExponent_le_primeRank [Finite F] {p e : ℕ} [Fact p.Prime] [CharP F p]
    (hc : Nat.card F = p ^ e) : 2 * e ≤ primeRank p PSL(3,F) := by
  let f := (PSL3Even.UnipotentGeometry.projective F).comp
    (PSL3Even.UnipotentGeometry.axis₁ F)
  refine primeRank_ge_of_elementary_embedding (A := Multiplicative (F × F))
    ?_ ?_ f
    ((PSL3Even.UnipotentGeometry.projective_injective F).comp
      (PSL3Even.UnipotentGeometry.axis₁_injective F))
  · intro v
    change p • v.toAdd = 0
    ext <;> simp [nsmul_eq_mul]
  · change Nat.card (F × F) = _
    rw [Nat.card_prod, hc, ← pow_add]
    congr 1
    omega

end Matrix.PSL3.DefiningRank
