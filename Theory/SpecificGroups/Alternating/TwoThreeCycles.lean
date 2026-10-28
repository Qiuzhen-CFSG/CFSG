module

public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.Data.ZMod.Basic

/-!
# Two independent three-cycles in alternating groups

Translations on two disjoint three-point blocks embed `C₃ × C₃` in `Aₙ`
for `n ≥ 6`. Their exponent is three, so every permutation in the image
is even. The embedding witnesses the strict lower bound on three-rank.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.32(3), printed p.1133, invoking the rank hypothesis of A.3.18.
The construction follows the three-block argument in `Alternating.ThreeRank`.
-/

namespace alternatingGroup.TwoThreeCycles

private abbrev E := Fin 2 → Multiplicative (ZMod 3)

private def blockAction : E →* Equiv.Perm (Fin 2 × ZMod 3) where
  toFun a := Equiv.prodCongrRight (fun i => Equiv.addLeft (a i).toAdd)
  map_one' := by ext x <;> simp
  map_mul' a b := by ext x <;> simp

private theorem blockAction_injective : Function.Injective blockAction := by
  intro a b h
  funext i
  have h' := congrArg (fun f : Equiv.Perm (Fin 2 × ZMod 3) => (f (i, 0)).2) h
  simpa [blockAction] using h'

private theorem cube (a : E) : a ^ 3 = 1 := by
  funext i
  change Multiplicative.ofAdd (3 • (a i).toAdd) = Multiplicative.ofAdd 0
  congr 1
  simp only [nsmul_eq_mul]
  exact zero_mul _

private theorem card : Nat.card E = 3 ^ 2 := by
  simp [E, Nat.card_eq_fintype_card]

private noncomputable def points {n : ℕ} (hn : 6 ≤ n) : (Fin 2 × ZMod 3) ↪ Fin n :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using hn))

private noncomputable def action {n : ℕ} (hn : 6 ≤ n) : E →* Equiv.Perm (Fin n) :=
  (Equiv.Perm.viaEmbeddingHom (points hn)).comp blockAction

/-- The action of the two independent three-cycles. -/
public noncomputable def embedding {n : ℕ} (hn : 6 ≤ n) :
    (Fin 2 → Multiplicative (ZMod 3)) →* alternatingGroup (Fin n) :=
  (action hn).codRestrict _ (by
    intro a
    change Equiv.Perm.sign (action hn a) = 1
    have h3 : Equiv.Perm.sign (action hn a) ^ 3 = 1 := by
      rw [← map_pow, ← map_pow, cube, map_one, map_one]
    have h2 := Int.units_sq (Equiv.Perm.sign (action hn a))
    simpa [pow_succ, h2] using h3)

public theorem embedding_injective {n : ℕ} (hn : 6 ≤ n) :
    Function.Injective (embedding hn) := by
  intro a b h
  exact blockAction_injective (Equiv.Perm.viaEmbeddingHom_injective (points hn)
    (congrArg Subtype.val h))

/-- In particular, `A₈` has three-rank greater than one. -/
public theorem two_le_primeRank {n : ℕ} (hn : 6 ≤ n) :
    2 ≤ primeRank 3 (alternatingGroup (Fin n)) :=
  primeRank_ge_of_elementary_embedding cube card (embedding hn) (embedding_injective hn)

end alternatingGroup.TwoThreeCycles
