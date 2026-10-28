module

public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# An elementary eight in every alternating group of degree at least eight

The regular translations of the three-dimensional binary vector space are
involutions with four transpositions, hence even permutations. Extending this
faithful action by fixed points gives the lower bound on two-rank used in the
known-simple sieve of Aschbacher–Smith A.2.12, printed p.36.
-/

namespace alternatingGroup.TwoRankSieve
private abbrev E := Multiplicative (Fin 3 → ZMod 2)

private def translations : E →* Equiv.Perm (Fin 3 → ZMod 2) where
  toFun a := Equiv.addLeft a.toAdd
  map_one' := by ext b i; simp
  map_mul' a b := by ext c i; simp

private theorem translations_injective : Function.Injective translations := by
  intro a b hab
  have he := congrArg (fun p : Equiv.Perm (Fin 3 → ZMod 2) => p 0) hab
  simpa [translations] using he

private theorem square (a : E) : a^2=1 := by
  change 2 • a.toAdd = 0
  funext i
  simp only [nsmul_eq_mul]
  exact zero_mul _

private theorem translations_sign (a : E) : Equiv.Perm.sign (translations a) = 1 := by
  classical
  by_cases ha : a = 1
  · simp [ha]
  have hp : translations a ^ 2 = 1 := by rw [← map_pow, square, map_one]
  have hfixed : IsEmpty (Function.fixedPoints (translations a)) := by
    constructor
    rintro ⟨b,hb⟩
    apply ha
    change a.toAdd + b = b at hb
    change a.toAdd = 0
    exact add_right_cancel (hb.trans (zero_add b).symm)
  have hc : Fintype.card (Function.fixedPoints (translations a)) = 0 := Fintype.card_eq_zero
  rw [Equiv.Perm.sign_of_pow_two_eq_one hp, hc]
  norm_num [Fintype.card_fun]
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Int.units_sq]

private noncomputable def points {n : ℕ} (hn : 8 ≤ n) : (Fin 3 → ZMod 2) ↪ Fin n :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using hn))

/-- Regular translations on eight points are even permutations, and extend
faithfully to every larger alternating group. -/
public noncomputable def embedding {n : ℕ} (hn : 8 ≤ n) : Multiplicative (Fin 3 → ZMod 2) →* alternatingGroup (Fin n) :=
  ((Equiv.Perm.viaEmbeddingHom (points hn)).comp translations).codRestrict _ (by
    intro a
    change Equiv.Perm.sign ((translations a).viaEmbedding (points hn)) = 1
    rw [Equiv.Perm.viaEmbedding, Equiv.Perm.sign_extendDomain]
    exact translations_sign a)

public theorem embedding_injective {n : ℕ} (hn : 8 ≤ n) : Function.Injective (embedding hn) := by
  intro a b hab
  exact translations_injective (Equiv.Perm.viaEmbeddingHom_injective (points hn)
    (congrArg Subtype.val hab))

public theorem three_le_primeRank {n : ℕ} (hn : 8 ≤ n) :
    3 ≤ primeRank 2 (alternatingGroup (Fin n)) :=
  primeRank_ge_of_elementary_embedding square (by simp [E])
    (embedding hn) (embedding_injective hn)

end alternatingGroup.TwoRankSieve
