module

public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.Data.ZMod.Basic

/-!
# Three disjoint three-cycles in alternating groups

For n ≥ 9, independent translations on three blocks of size three embed
(C₃)³ in Aₙ. The action is faithful, and its exponent three forces every
permutation to have positive sign. This proves that the 3-rank is at least
three, the obstruction used for the A₉ and A₁₁ sections in
Aschbacher--Smith, *The Classification of Quasithin Groups*, A.2.15--19.
-/

namespace alternatingGroup.ThreeRank
private abbrev E := Fin 3 → Multiplicative (ZMod 3)

private def blockAction : E →* Equiv.Perm (Fin 3 × ZMod 3) where
  toFun a := Equiv.prodCongrRight (fun i => Equiv.addLeft (a i).toAdd)
  map_one' := by ext x <;> simp
  map_mul' a b := by ext x <;> simp

private theorem blockAction_injective : Function.Injective blockAction := by
  intro a b h
  funext i
  have h' := congrArg (fun f : Equiv.Perm (Fin 3 × ZMod 3) => (f (i, 0)).2) h
  simpa [blockAction] using h'

private theorem cube (a : E) : a ^ 3 = 1 := by
  funext i
  change Multiplicative.ofAdd (3 • (a i).toAdd) = Multiplicative.ofAdd 0
  congr 1
  simp only [nsmul_eq_mul]
  exact zero_mul _

private theorem card : Nat.card E = 3 ^ 3 := by
  simp [E, Nat.card_eq_fintype_card]

private noncomputable def points {n : ℕ} (hn : 9 ≤ n) : (Fin 3 × ZMod 3) ↪ Fin n :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using hn))

private noncomputable def action {n : ℕ} (hn : 9 ≤ n) : E →* Equiv.Perm (Fin n) :=
  (Equiv.Perm.viaEmbeddingHom (points hn)).comp blockAction

/-- Faithful even permutations on three independent blocks of size three. -/
public noncomputable def embedding {n : ℕ} (hn : 9 ≤ n) : (Fin 3 → Multiplicative (ZMod 3)) →* alternatingGroup (Fin n) :=
  (action hn).codRestrict _ (by
    intro a
    change Equiv.Perm.sign (action hn a) = 1
    have h3 : Equiv.Perm.sign (action hn a) ^ 3 = 1 := by
      rw [← map_pow, ← map_pow, cube, map_one, map_one]
    have h2 := Int.units_sq (Equiv.Perm.sign (action hn a))
    simpa [pow_succ, h2] using h3)

public theorem embedding_injective {n : ℕ} (hn : 9 ≤ n) : Function.Injective (embedding hn) := by
  intro a b h
  exact blockAction_injective (Equiv.Perm.viaEmbeddingHom_injective (points hn)
    (congrArg Subtype.val h))

/-- Three disjoint three-cycles witness 3-rank at least three. -/
public theorem three_le_primeRank {n : ℕ} (hn : 9 ≤ n) :
    3 ≤ primeRank 3 (alternatingGroup (Fin n)) :=
  primeRank_ge_of_elementary_embedding cube card (embedding hn) (embedding_injective hn)
end alternatingGroup.ThreeRank
