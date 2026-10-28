module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FinitePrimes
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FiniteSource.ExceptionalOdd.Rudvalis
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FiniteSource.ExceptionalOdd.Tits
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FiniteSource.ExceptionalOdd.HigmanSims
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FiniteSource.ExceptionalOdd.Held
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FiniteSource.ExceptionalOdd.TrialityTwo
/-!
# Large-prime source exclusions from the actual finite Sylow pairs

The proved component-order restrictions identify the only possible prime in
each row. The specialized local proofs then exclude Ru, Tits, HS, Held and
binary triality using the original pair, full Sylow subgroup and actual model
map. No prime equality, local coverage or two-core conclusion remains a
hypothesis. The two Janko leaves are independent remaining source arguments.

Source: Aschbacher–Smith A.3.15, pp.50–51, and Proposition 1.3.4, pp.510–511.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source
variable {J : Type*} [Group J] [Finite J] {D B : Subgroup J} {S : Sylow 2 J} {p : ℕ}

theorem not_rudvalis [Group.IsPerfect D]
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (e : D ≃* Rudvalis.Model) : False := by
  have he := prime_eq_five_of_rudvalis hA hB e
  subst p
  exact ExceptionalOdd.not_rudvalis hA hB e

theorem not_tits [Group.IsPerfect D]
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (e : D ≃* Tits.ParrottGroup) : False := by
  have he := prime_eq_five_of_tits hA hB e
  subst p
  exact ExceptionalOdd.not_tits hA hB e

theorem not_higmanSims
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (e : D ≃* Sporadic.LeechRelated.HS.Carrier) : False := by
  have he := prime_eq_five_of_higmanSims hA hB e
  subst p
  exact ExceptionalOdd.not_higmanSims hA hB e

theorem not_held
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (e : D ≃* Held.He) : False :=
  ExceptionalOdd.not_held (prime_five_or_seven_of_held hA hB e) hA hB e
theorem not_triality_two
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (hm : Triality.Standard.IsTrialityGroupAt 2 D) : False := by
  have he := prime_eq_seven_of_triality hA hB hm
  subst p
  exact ExceptionalOdd.not_triality_two hA hB hm
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source
