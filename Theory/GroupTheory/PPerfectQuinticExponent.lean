module

public import Theory.GroupTheory.SimpleFiveSmallSectionAction

/-!
# Exponent-six images of a two-perfect quintic extension

A two-perfect group whose two-core quotient has order five has no
nontrivial image of exponent dividing six. Cauchy's theorem makes the
image order prime to five, so the proved prime-residual generation theorem
kills the whole image. No restriction on the other primes in the ambient
codomain, and no solvability hypothesis, is needed.

Source application: the actual outer action in Aschbacher--Smith 6.1.4,
printed pp.665--666, with the odd-prime ternary outer exponent from A.3.18.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Finite G] [Group H]

/-- The whole image vanishes when its sixth powers vanish. -/
theorem hom_eq_one_of_twoPerfect_quintic_of_sixth_power
    (hG : IsPPerfect 2 G) (hfive : Nat.card (G ⧸ pCore 2 G) = 5)
    (f : G →* H) (hpow : ∀ g, f g ^ 6 = 1) : f = 1 := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let : IsSimpleGroup (G ⧸ pCore 2 G) := isSimpleGroup_of_prime_card hfive
  have hcop : Nat.Coprime 5 (Nat.card f.range) := by
    apply Nat.prime_five.coprime_iff_not_dvd.mpr
    intro hd
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 5 hd
    have hp : x ^ 6 = 1 := by
      apply Subtype.ext
      obtain ⟨g,hg⟩ := x.property
      change (x : H) ^ 6 = 1
      rw [←hg]
      exact hpow g
    have hh := orderOf_dvd_of_pow_eq_one hp
    rw [hx] at hh
    norm_num at hh
  have hz := hom_eq_one_of_twoPerfect_simple_five_section hG
    (by rw [hfive]) f.rangeRestrict hcop
  ext g
  exact congrArg Subtype.val (DFunLike.congr_fun hz g)

end Theory.GroupTheory
