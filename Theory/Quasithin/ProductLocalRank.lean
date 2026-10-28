module
public import Theory.Quasithin.LocalRankEmbedding
public import Theory.GroupTheory.PrimeRankProduct
public import Mathlib.Order.Lattice.Nat
/-!
# Local prime rank in a finite direct product

Projecting a nontrivial two-subgroup to either factor puts its normalizer
inside the corresponding product of a local normalizer and the other factor.
Conversely a two-local in either factor gives a two-local times the other
factor. Thus, when both factors have two-locals, the local prime rank is the
maximum of the two sums of local and ordinary ranks.

In particular, replacing one factor by a group with no larger ordinary or
local prime rank cannot increase the product's local rank. This supplies the
literal direct-product transfer used in Aschbacher–Smith A.2.12(III), p.37.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.Quasithin.ProductLocalRank
variable {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]

private theorem attained (p : ℕ) (h : ∃ M : Subgroup A, IsTwoLocal M) :
    ∃ M : Subgroup A, IsTwoLocal M ∧ primeRank p M = twoLocalPrimeRank p A := by
  have hb : BddAbove {n : ℕ | ∃ M : Subgroup A, IsTwoLocal M ∧ n ≤ primeRank p M} := by
    refine ⟨primeRank p A, ?_⟩
    rintro n ⟨M, _, hn⟩
    exact hn.trans (primeRank_le_of_injective p M.subtype M.subtype_injective)
  have he : {n : ℕ | ∃ M : Subgroup A, IsTwoLocal M ∧ n ≤ primeRank p M}.Nonempty := by
    obtain ⟨M, hM⟩ := h
    exact ⟨0, M, hM, Nat.zero_le _⟩
  obtain ⟨M, hM, hle⟩ := Nat.sSup_mem he hb
  exact ⟨M, hM, (hM.primeRank_le p).antisymm hle⟩

omit [Finite A] [Finite B] in
private theorem normalizer_prod (P : Subgroup A) (Q : Subgroup B) :
    normalizer (P.prod Q : Set (A × B)) =
      (normalizer (P : Set A)).prod (normalizer (Q : Set B)) := by
  ext g
  simp only [Subgroup.mem_prod, Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    constructor
    · intro x
      simpa using h (x, 1)
    · intro x
      simpa using h (1, x)
  · rintro ⟨hP, hQ⟩ ⟨x,y⟩
    exact (hP x).and (hQ y)

omit [Finite A] [Finite B] in
private theorem prod_top_isTwoLocal {M : Subgroup A} (hM : IsTwoLocal M) :
    IsTwoLocal (M.prod (⊤ : Subgroup B)) := by
  obtain ⟨Q, hQ, hpQ, rfl⟩ := hM
  have he : Q.prod (⊥ : Subgroup B) = Q.map (MonoidHom.inl A B) := by
    ext x
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨x.1, hx, Prod.ext rfl (by simpa using hy.symm)⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, rfl⟩
  refine ⟨Q.prod ⊥, ?_, ?_, ?_⟩
  · rw [he]
    exact fun hh => hQ ((map_eq_bot_iff_of_injective Q (fun _ _ h => congrArg Prod.fst h)).mp hh)
  · rw [he]
    exact hpQ.map _
  · rw [normalizer_prod, normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup B).Normal)]

theorem local_add_ordinary_le (p : ℕ) [Fact p.Prime]
    (hA : ∃ M : Subgroup A, IsTwoLocal M) :
    twoLocalPrimeRank p A + primeRank p B ≤ twoLocalPrimeRank p (A × B) := by
  obtain ⟨M, hM, hm⟩ := attained p hA
  have hr := (prod_top_isTwoLocal (B := B) hM).primeRank_le p
  rw [primeRank_equiv p (M.prodEquiv (⊤ : Subgroup B)), primeRank_prod_eq_add,
    primeRank_equiv p (topEquiv : (⊤ : Subgroup B) ≃* B), hm] at hr
  exact hr

private theorem projected_normalizer_rank_le (p : ℕ) [Fact p.Prime]
    (Q : Subgroup (A × B)) (hpQ : IsPGroup 2 Q)
    (hQ : Q.map (MonoidHom.fst A B) ≠ ⊥) :
    primeRank p (normalizer (Q : Set (A × B))) ≤
      twoLocalPrimeRank p A + primeRank p B := by
  let R := Q.map (MonoidHom.fst A B)
  have hr : IsTwoLocal (normalizer (R : Set A)) := ⟨R, hQ, hpQ.map _, rfl⟩
  have hn : normalizer (Q : Set (A × B)) ≤ (normalizer (R : Set A)).prod ⊤ := by
    intro x hx
    exact ⟨le_normalizer_map (MonoidHom.fst A B) ⟨x, hx, rfl⟩, mem_top _⟩
  have hb := primeRank_le_of_injective p (inclusion hn) (inclusion_injective hn)
  rw [primeRank_equiv p ((normalizer (R : Set A)).prodEquiv (⊤ : Subgroup B)),
    primeRank_prod_eq_add, primeRank_equiv p (topEquiv : (⊤ : Subgroup B) ≃* B)] at hb
  exact hb.trans (Nat.add_le_add_right (hr.primeRank_le p) _)

theorem local_prod_le (p : ℕ) [Fact p.Prime] :
    twoLocalPrimeRank p (A × B) ≤ max
      (twoLocalPrimeRank p A + primeRank p B)
      (primeRank p A + twoLocalPrimeRank p B) := by
  apply (twoLocalPrimeRank_le_iff p _).mpr
  rintro M ⟨Q, hQ, hpQ, rfl⟩
  by_cases hfst : Q.map (MonoidHom.fst A B) = ⊥
  · have hsnd : Q.map (MonoidHom.snd A B) ≠ ⊥ := by
      intro hsnd
      apply hQ
      apply eq_bot_iff.mpr
      intro x hx
      have ha : x.1 = 1 := by
        have := show x.1 ∈ Q.map (MonoidHom.fst A B) from ⟨x, hx, rfl⟩
        simpa [hfst] using this
      have hb : x.2 = 1 := by
        have := show x.2 ∈ Q.map (MonoidHom.snd A B) from ⟨x, hx, rfl⟩
        simpa [hsnd] using this
      exact Prod.ext ha hb
    let R := Q.map (MonoidHom.snd A B)
    have hr : IsTwoLocal (normalizer (R : Set B)) := ⟨R, hsnd, hpQ.map _, rfl⟩
    have hn : normalizer (Q : Set (A × B)) ≤ (⊤ : Subgroup A).prod (normalizer (R : Set B)) := by
      intro x hx
      exact ⟨mem_top _, le_normalizer_map (MonoidHom.snd A B) ⟨x, hx, rfl⟩⟩
    have hb := primeRank_le_of_injective p (inclusion hn) (inclusion_injective hn)
    rw [primeRank_equiv p ((⊤ : Subgroup A).prodEquiv (normalizer (R : Set B))),
      primeRank_prod_eq_add, primeRank_equiv p (topEquiv : (⊤ : Subgroup A) ≃* A)] at hb
    exact (hb.trans (Nat.add_le_add_left (hr.primeRank_le p) _)).trans (le_max_right _ _)
  · exact (projected_normalizer_rank_le p Q hpQ hfst).trans (le_max_left _ _)

theorem ordinary_add_local_le (p : ℕ) [Fact p.Prime]
    (hB : ∃ M : Subgroup B, IsTwoLocal M) :
    primeRank p A + twoLocalPrimeRank p B ≤ twoLocalPrimeRank p (A × B) := by
  have h := (local_add_ordinary_le (B := A) p hB).trans
    (twoLocalPrimeRank_le_of_injective p (MulEquiv.prodComm : B × A ≃* A × B).toMonoidHom
      (MulEquiv.prodComm : B × A ≃* A × B).injective)
  simpa only [Nat.add_comm] using h

theorem local_prod_eq (p : ℕ) [Fact p.Prime]
    (hA : ∃ M : Subgroup A, IsTwoLocal M)
    (hB : ∃ M : Subgroup B, IsTwoLocal M) :
    twoLocalPrimeRank p (A × B) = max
      (twoLocalPrimeRank p A + primeRank p B)
      (primeRank p A + twoLocalPrimeRank p B) := by
  apply (local_prod_le p).antisymm
  exact max_le (local_add_ordinary_le p hA) (ordinary_add_local_le p hB)

theorem local_prod_le_of_factor_ranks {A' : Type*} [Group A'] [Finite A']
    (p : ℕ) [Fact p.Prime]
    (hA : ∃ M : Subgroup A, IsTwoLocal M)
    (hB : ∃ M : Subgroup B, IsTwoLocal M)
    (hr : primeRank p A' ≤ primeRank p A)
    (hl : twoLocalPrimeRank p A' ≤ twoLocalPrimeRank p A) :
    twoLocalPrimeRank p (A' × B) ≤ twoLocalPrimeRank p (A × B) := by
  rw [local_prod_eq p hA hB]
  exact (local_prod_le p).trans (max_le_max (Nat.add_le_add_right hl _)
    (Nat.add_le_add_right hr _))

end Theory.Quasithin.ProductLocalRank
