module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.Reduction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.GroupAction.SimpleCosets
public import Theory.GroupTheory.SubgroupProductCard
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The PSL₂(9) pair exclusion, including central covers

In a simple group of order 360, a permuting product of a subgroup of order
nine and a Sylow two-subgroup would have order 72 and index five. The faithful
coset action would then force 360 to divide 5!, a contradiction.

The central-kernel reduction gives an image of order nine or 27 for every
nonreducible pair in a quasisimple cover. Lagrange eliminates order 27; the
index-five argument eliminates order nine. Thus this argument handles every
central cover directly, without any Schur-multiplier hypothesis. The PSL₂(9)
identification is used through its actual matrix-group order formula.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528), the L₂(3²) = A₆ exclusion.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical
universe u
variable {Q : Type u} [Group Q] [Finite Q]

private def productSubgroup (R S : Subgroup Q)
    (hp : (R : Set Q) * (S : Set Q) = (S : Set Q) * (R : Set Q)) : Subgroup Q where
  carrier := (R : Set Q) * (S : Set Q)
  one_mem' := ⟨1, R.one_mem, 1, S.one_mem, mul_one 1⟩
  mul_mem' := by
    rintro x y ⟨r, hr, s, hs, rfl⟩ ⟨r', hr', s', hs', rfl⟩
    obtain ⟨a, ha, b, hb, he⟩ := Set.mem_mul.mp (hp.symm ▸ Set.mul_mem_mul hs hr')
    refine ⟨r * a, R.mul_mem hr ha, b * s', S.mul_mem hb hs', ?_⟩
    calc
      (r * a) * (b * s') = r * (a * b) * s' := by group
      _ = (r * s) * (r' * s') := by rw [he]; group
  inv_mem' := by
    rintro x ⟨r, hr, s, hs, rfl⟩
    rw [mul_inv_rev, hp]
    exact Set.mul_mem_mul (S.inv_mem hs) (R.inv_mem hr)

theorem not_permuting_of_simple_card_360 [IsSimpleGroup Q]
    (hQ : Nat.card Q = 360) (S : Sylow 2 Q) (R : Subgroup Q)
    (hR : Nat.card R = 9) :
    (R : Set Q) * (S : Set Q) ≠ (S : Set Q) * (R : Set Q) := by
  intro hp
  have hs : Nat.card S = 8 := by
    rw [S.card_eq_multiplicity, hQ, show 360 = 2 ^ 3 * 45 by decide,
      Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.prime_two.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 45)]
    norm_num
  have hd : Disjoint R (S : Subgroup Q) :=
    disjoint_of_coprime_natCard (by rw [hR, hs]; norm_num)
  let H := productSubgroup R S hp
  have hH : Nat.card H = 72 := by
    have hh := card_set_mul_mul_card_inf R (S : Subgroup Q)
    rw [disjoint_iff.mp hd, card_bot, mul_one, hR, hs] at hh
    exact hh
  have hi : H.index = 5 := by
    have hh := H.card_mul_index
    rw [hH, hQ] at hh
    omega
  have hn : H ≠ ⊤ := by intro he; rw [he, index_top] at hi; omega
  have hh := H.card_dvd_factorial_index_of_simple hn
  rw [hQ, hi] at hh
  norm_num at hh

theorem reducible_of_central_quotient_card_360 {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) (hQ : Nat.card (Q ⧸ center Q) = 360) :
    PairReducible (S : Subgroup Q) R := by
  by_contra hn
  let _ := h.quasisimple.simple
  let q := QuotientGroup.mk' (center Q)
  let S' := S.mapSurjective (QuotientGroup.mk'_surjective (center Q))
  have hR : Nat.card (R.map q) = 9 := by
    rcases central_image_card h hn with hh | hh
    · exact hh
    · have hd := (R.map q).card_subgroup_dvd_card
      rw [hh, hQ] at hd
      norm_num at hd
  apply not_permuting_of_simple_card_360 hQ S' (R.map q) hR
  have hp := congrArg (Set.image q) h.permutes
  change (R.map q : Set (Q ⧸ center Q)) *
      ((S : Subgroup Q).map q : Set (Q ⧸ center Q)) =
      ((S : Subgroup Q).map q : Set (Q ⧸ center Q)) * (R.map q : Set (Q ⧸ center Q))
  simpa only [Set.image_mul, Subgroup.coe_map, Sylow.coe_coe] using hp

theorem reducible_of_psl_two_nine {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) (hm : ClassicalGroup.IsPSL (Q ⧸ center Q) 2 9) :
    PairReducible (S : Subgroup Q) R := by
  apply reducible_of_central_quotient_card_360 h
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have hh := Atlas.ExceptionalSupport.card_psl_mul (F := F) 2
  rw [← Nat.card_congr e.toEquiv, hF] at hh
  norm_num [Fin.prod_univ_succ] at hh
  omega

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical
