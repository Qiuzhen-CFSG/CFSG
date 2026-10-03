module
public import Stellmacher.MainType.TenOne
public import Theory.GroupTheory.NonsolvableTwoLocal

/-!
# A nonsolvable two-local in the Mathieu local type

The source-local M12 type includes an involution in its embedded graph group
whose image has nonsolvable centralizer in the ambient group. Injectivity
preserves the involution's nonidentity, and the homomorphism preserves its
square. The proved involution-centralizer reduction then gives an actual
nonsolvable two-local subgroup of the ambient group.

This proves the M12 part of the final addendum to Stellmacher's Theorem 1
from the definition itself, with no terminal-context or global hypothesis.
Source: Stellmacher, Journal of Algebra190 (1997), Theorem1 and (10.1)(a).
-/

namespace Stellmacher
universe u

public theorem exists_nonsolvable_twoLocal_of_mathieuTwelve_type
    {H : Type u} [Group H] [Finite H] (htype : IsOfMathieuTwelveType H) :
    ∃ U : Subgroup H, IsTwoLocal U ∧ ¬ Group.IsSolvable U := by
  obtain ⟨data⟩ := htype
  let _ := data.groupK
  let _ := data.finiteK
  obtain ⟨point, hinvolution, _, _, hnonsolvable⟩ := data.caseA.nonsolvable_centralizer
  have hne : data.embedding point ≠ 1 := by
    intro heq
    exact hinvolution.1
      (data.embedding_injective (heq.trans (map_one data.embedding).symm))
  have hpow : data.embedding point ^ 2 = 1 := by
    rw [← map_pow, hinvolution.2, map_one]
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Theory.GroupTheory.exists_nonsolvable_twoLocal_of_involution_centralizer
    (orderOf_eq_prime hpow hne) hnonsolvable

end Stellmacher
