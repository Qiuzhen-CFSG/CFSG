module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Covers
public import Theory.Mathieu.M12.Basic
public import Theory.Mathieu.M12.SylowOvergroups.Coverage
public import Theory.Mathieu.M12.SylowOvergroups.Obstructions
public import Theory.GroupTheory.SubgroupProductCard
public import Theory.GroupTheory.PResidual.SubnormalSupplement

/-!
# Excluding the M₁₂ Sylow pair

An odd complement in `XiOddQuotient 3` has order nine or twenty-seven.
If it permutes with a Sylow two-subgroup, their product is an actual subgroup
of order 576 or 1728. The checked Sylow double-coset enumeration and its
prime-order words place every Sylow overgroup of order prime to 55 in one of
the two marked parabolics, both of order 192. This is a contradiction.

Thus no such pair exists in the concrete M₁₂ model, without needing the other
`PairInput` hypotheses. The parent module handles central covers and transport.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511/PDF p.528;
Aschbacher, *Overgroups of Sylow subgroups in sporadic groups*, Memoirs AMS
60 (1986), no.343; GLS3 Table 5.3b. Exhaustiveness here is proved by finite
coset enumeration, not inferred from the existence of the two parabolics.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Sporadic.Mathieu Sporadic.Mathieu.M12SmallPair
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.MathieuTwelve

theorem sylow_card (S : Sylow 2 M12) : Nat.card S = 64 := by
  calc
    Nat.card S = Nat.card commonSylow := Nat.card_congr (Sylow.equiv S commonSylow).toEquiv
    _ = 64 := card_sylowCandidate

/-- Transport the marked subgroup bound to any Sylow subgroup. -/
theorem overgroup_card_le (S : Sylow 2 M12) (H : Subgroup M12)
    (hS : (S : Subgroup M12) ≤ H)
    (h5 : ¬ 5 ∣ Nat.card H) (h11 : ¬ 11 ∣ Nat.card H) : Nat.card H ≤ 192 := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M12 S commonSylow
  let e : MulAut M12 := MulAut.conj g
  have hmap : (S : Subgroup M12).map e.toMonoidHom = sylowCandidate := by
    change ((g • S : Sylow 2 M12) : Subgroup M12) = sylowCandidate
    rw [hg]
    rfl
  have hm : sylowCandidate ≤ H.map e.toMonoidHom := by
    rw [← hmap]
    exact map_mono hS
  have hc : Nat.card (H.map e.toMonoidHom) = Nat.card H :=
    (Nat.card_congr (e.subgroupMap H).toEquiv).symm
  have hb := SylowOvergroups.card_le_of_covers SylowOvergroups.covers
    (H.map e.toMonoidHom) hm (by simpa only [hc] using h5) (by simpa only [hc] using h11)
  rwa [hc] at hb

theorem product_card {S : Sylow 2 M12} {R : Subgroup M12}
    (hR : XiOddQuotient 3 R)
    (hperm : (R : Set M12) * (S : Set M12) = (S : Set M12) * (R : Set M12)) :
    Nat.card (R ⊔ (S : Subgroup M12) : Subgroup M12) = Nat.card R * 64 := by
  have hd : Disjoint R (S : Subgroup M12) :=
    hR.isPGroup.disjoint_of_coprime S.isPGroup' (by decide)
  have hc := card_set_mul_mul_card_inf R (S : Subgroup M12)
  rw [hd.eq_bot, card_bot, mul_one,
    ← coe_sup_of_set_mul_comm R (S : Subgroup M12) hperm, sylow_card S] at hc
  exact hc

theorem product_card_cases {S : Sylow 2 M12} {R : Subgroup M12}
    (hR : XiOddQuotient 3 R)
    (hperm : (R : Set M12) * (S : Set M12) = (S : Set M12) * (R : Set M12)) :
    Nat.card (R ⊔ (S : Subgroup M12) : Subgroup M12) = 576 ∨
    Nat.card (R ⊔ (S : Subgroup M12) : Subgroup M12) = 1728 := by
  rw [product_card hR hperm]
  rcases hR with ⟨_, hc⟩ | ⟨_, hc, _⟩
  · exact Or.inl (by rw [hc]; norm_num)
  · exact Or.inr (by rw [hc]; norm_num)

/-- Permutability alone excludes the noncyclic odd complement in M₁₂. -/
theorem no_pair (S : Sylow 2 M12) (R : Subgroup M12) (hR : XiOddQuotient 3 R)
    (hperm : (R : Set M12) * (S : Set M12) = (S : Set M12) * (R : Set M12)) : False := by
  have hc := product_card_cases hR hperm
  have h5 : ¬ 5 ∣ Nat.card (R ⊔ (S : Subgroup M12) : Subgroup M12) := by
    rcases hc with h | h <;> rw [h] <;> norm_num
  have h11 : ¬ 11 ∣ Nat.card (R ⊔ (S : Subgroup M12) : Subgroup M12) := by
    rcases hc with h | h <;> rw [h] <;> norm_num
  have hb := overgroup_card_le S (R ⊔ (S : Subgroup M12)) le_sup_right h5 h11
  rcases hc with h | h <;> omega

/-- The M₁₂ branch of the source Sylow-pair sieve. -/
theorem pairReducible (S : Sylow 2 M12) (R : Subgroup M12) (h : PairInput S R) :
    PairReducible (S : Subgroup M12) R :=
  (no_pair S R h.oddComplement h.permutes).elim

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.MathieuTwelve
