module

public import Theory.Alternating.TripleSevenLocalRank.CentralSix
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupAction.Quotient
public import Theory.ElementaryAbelian.Injective

/-!
# Cubic rank in preimages under central covers of A₆

For a central cubic extension of A₆, the inverse image of any subgroup
of order three has order nine. The checked exponent theorem for the
actual alternating covers makes this preimage elementary abelian.
Consequently any subgroup downstairs whose order is divisible by three
has preimage of three-rank at least two.

The source consumer is the triple-cover exclusion in Aschbacher–Smith
13.4.8, printed p.905. The exponent input is the genuine alternating-cover
calculation used in A.2.12(I.i), printed p.36.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.SpecificGroups.AlternatingSix.CubicPreimageRank
variable {E : Type*} [Group E] [Finite E]

theorem two_le_rank_preimage (q : E →* alternatingGroup (Fin 6))
    (hq : Function.Surjective q) (hc : q.ker ≤ center E) (hk : Nat.card q.ker = 3)
    (S : Subgroup (alternatingGroup (Fin 6))) (hS : 3 ∣ Nat.card S) :
    2 ≤ primeRank 3 (S.comap q) := by
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := S) 3 hS
  let P := (zpowers a).map S.subtype
  have hP : Nat.card P = 3 := by
    rw [card_map_of_injective S.subtype_injective,Nat.card_zpowers,ha]
  have hPS : P ≤ S := map_subtype_le _
  let B := P.comap q
  have hB : Nat.card B = 3 ^ 2 := by
    rw [card_eq_card_quotient_mul_card_subgroup (q.ker.subgroupOf B),
      card_quotient_subgroupOf_comap_eq (f := q) (hf := hq) (H := P),
      Nat.card_congr (subgroupOfEquivOfLe (ker_le_comap (f := q) (H := P))).toEquiv,
      hP,hk]
    norm_num
  let : IsElementaryAbelian 3 B := {
    toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq hB
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply Subtype.ext
      apply GLS3.Chapter5.OddCentralCovers.central_six_cube_eq_one_of_ninth q hq hc hk
      exact congrArg Subtype.val (hB ▸ pow_card_eq_one' (x := x)) }
  have hr : 2 ≤ primeRank 3 B := by
    let : IsElementaryAbelian 3 (⊤ : Subgroup B) := IsElementaryAbelian.of_injective
      (⊤ : Subgroup B).subtype (⊤ : Subgroup B).subtype_injective
    apply IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup B)
    simpa using hB
  exact hr.trans (primeRank_mono 3 (comap_mono hPS))
end Theory.SpecificGroups.AlternatingSix.CubicPreimageRank
