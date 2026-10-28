module

public import Glauberman.DicksonUnipotent
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Defining-prime rank in PSL₂

The upper unipotent matrices give an injective image of the additive group of
`F` in PSL₂(F), in every characteristic. If `|F| = p^e`, that group has exponent
`p` and order `p^e`, so it witnesses defining-prime rank at least `e`.

Source application: the field-degree bound in Aschbacher–Smith E.2.2(2c),
printed pp.215–216. In a strongly quasithin group the odd root rank is at most
two. This argument does not use the classification of Sylow overgroups.
-/

public section

namespace Theory.PSL2
open BenderSuzuki.MatrixGroups

/-- The actual upper root subgroup witnesses defining-prime rank at least `e`. -/
theorem root_prime_rank_ge (F : Type*) [Field F] [Finite F] {p e : ℕ}
    [Fact p.Prime] (hF : Nat.card F = p ^ e) :
    e ≤ primeRank p (PSL2MatrixGroup F) := by
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (p := p) (f := e)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let f := (Glauberman.Dickson.projectiveUnipotentAddChar F).toMonoidHom
  have hf : Function.Injective f := by
    intro a b hab
    exact Glauberman.Dickson.projectiveUnipotentAddChar_injective F hab
  apply primeRank_ge_of_elementary_embedding (A := Multiplicative F) ?_ ?_ f hf
  · intro a
    change p • a.toAdd = 0
    rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  · exact hF

end Theory.PSL2
