module

public import Theory.Quasithin.CoprimeRank
public import Theory.Quasithin.LocalRankEmbedding
public import Theory.GroupTheory.TwoLocalSurjective

/-!
# Local prime rank through an odd coprime kernel

Surjective homomorphisms with kernel coprime to p do not increase the
codomain's two-local p-rank: lift an actual two-local normalizer using the
Frattini argument, then lift its abelian p-subgroups. If the kernel also
has odd order, no nontrivial two-subgroup disappears, so the reverse
inequality follows by mapping each actual source normalizer.

Source: Aschbacher–Smith A.2.11, printed p.35. The oddness and coprimality
hypotheses are both retained; arbitrary quotient monotonicity is not used.
-/

public section
open Subgroup Theory.GroupTheory

private theorem kernel_restriction_coprime
    {G H A B : Type*} [Group G] [Group H] [Group A] [Group B]
    [Finite G] [Finite A] (f : G →* H) (g : A →* B)
    (a : A →* G) (ha : Function.Injective a) (b : B →* H)
    (h : b.comp g = f.comp a) (p : ℕ) (hc : Nat.Coprime p (Nat.card f.ker)) :
    Nat.Coprime p (Nat.card g.ker) := by
  let j : g.ker →* f.ker := (a.comp g.ker.subtype).codRestrict _ (by
    intro x
    change f (a x) = 1
    have hh : b (g (x : A)) = f (a (x : A)) := DFunLike.congr_fun h (x : A)
    rw [← hh]
    rw [show g x = 1 from x.property, map_one])
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    exact ha (congrArg Subtype.val he)
  exact hc.of_dvd_right (Subgroup.card_dvd_of_injective j hj)

variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

theorem twoLocalPrimeRank_le_of_surjective_of_coprime
    (p : ℕ) [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hc : Nat.Coprime p (Nat.card f.ker)) :
    twoLocalPrimeRank p H ≤ twoLocalPrimeRank p G := by
  apply (twoLocalPrimeRank_le_iff p _).mpr
  intro M hM
  obtain ⟨L, hL, _, g, hg, he⟩ := hM.exists_surjective_of_surjective f hf
  have hcomp : M.subtype.comp g = f.comp L.subtype := by ext x; exact he x
  have hgker := kernel_restriction_coprime f g L.subtype L.subtype_injective M.subtype
    hcomp p hc
  exact (primeRank_eq_of_surjective_of_coprime p g hg hgker).ge.trans (hL.primeRank_le p)

theorem twoLocalPrimeRank_le_of_coprime_ker
    (p : ℕ) [Fact p.Prime] (f : G →* H)
    (hc : Nat.Coprime p (Nat.card f.ker)) (ho : Nat.Coprime 2 (Nat.card f.ker)) :
    twoLocalPrimeRank p G ≤ twoLocalPrimeRank p H := by
  apply (twoLocalPrimeRank_le_iff p _).mpr
  rintro M ⟨Q, hQ, hpQ, rfl⟩
  have hR : Q.map f ≠ ⊥ := by
    intro he
    have hk : Q ≤ f.ker := (Subgroup.map_eq_bot_iff Q).mp he
    have hd : Disjoint Q f.ker := Subgroup.disjoint_of_coprime_natCard (by
      obtain ⟨n, hn⟩ := hpQ.exists_card_eq
      rw [hn]
      exact ho.pow_left n)
    exact hQ (le_bot_iff.mp (fun x hx => hd.le_bot ⟨hx, hk hx⟩))
  have hlocal : IsTwoLocal (normalizer (Q.map f : Set H)) :=
    ⟨Q.map f, hR, hpQ.map f, rfl⟩
  let N := normalizer (Q : Set G)
  let g := f.subgroupMap N
  have hgker := kernel_restriction_coprime f g N.subtype N.subtype_injective
    (N.map f).subtype rfl p hc
  calc
    primeRank p N = primeRank p (N.map f) :=
      primeRank_eq_of_surjective_of_coprime p g (f.subgroupMap_surjective N) hgker
    _ ≤ primeRank p (normalizer (Q.map f : Set H)) :=
      Theory.GroupTheory.primeRank_le_of_injective p (Subgroup.inclusion (Subgroup.le_normalizer_map f))
        (Subgroup.inclusion_injective _)
    _ ≤ twoLocalPrimeRank p H := hlocal.primeRank_le p

/-- A surjection with odd kernel coprime to p preserves two-local p-rank. -/
theorem twoLocalPrimeRank_eq_of_surjective_of_coprime
    (p : ℕ) [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hc : Nat.Coprime p (Nat.card f.ker)) (ho : Nat.Coprime 2 (Nat.card f.ker)) :
    twoLocalPrimeRank p G = twoLocalPrimeRank p H :=
  le_antisymm (twoLocalPrimeRank_le_of_coprime_ker p f hc ho)
    (twoLocalPrimeRank_le_of_surjective_of_coprime p f hf hc)
