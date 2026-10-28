module
public import Theory.SpecificGroups.Classical.EvenRankTwoOddRank
public import Theory.SpecificGroups.Classical.BinarySmallSylowOrders
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import GorensteinWalter.SL2UniversalCover
public import Theory.Mathieu.M11.Properties.Order
public import Theory.SpecificGroups.PSL3Three.Cardinality
public import CFSG.Quasithin.ClassicalModels
/-!
# The small and prime-linear targets in rank-two non-enlargement

Both actual source quotients have order divisible by 64. This excludes the
PSL₃(3), M₁₁ and A₆ targets. Their split tori also give an odd-prime rank-two
witness, unchanged by the original central two-kernel. Prime PSL₂ has cyclic
odd Sylows; the binary PSL₃(2) quotient has order 168 and therefore odd rank
at most one. These exclude the prime-linear and binary central-cover targets.
All fields, centers, quotients and faithful maps remain literal.

Source: Aschbacher–Smith 2.5.6, printed p.554.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement
variable {K C : Type*} [Group K] [Finite K] [Group C] [Finite C]

omit [Finite K] in
/-- The full two-part required for the actual small-target exclusions. -/
theorem sixty_four_dvd_card_of_model {n : ℕ} (hn : 1<n)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 (2^n) ∨
      ClassicalGroup.IsPSp (K ⧸ center K) 2 (2^n)) : 64 ∣ Nat.card K := by
  apply dvd_trans _ (center K).card_quotient_dvd_card
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv]
    exact Theory.ClassicalSmallSylow.binary_psl3_two_power_dvd hF (by omega : 6≤3*n)
  · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    rw [Nat.card_congr e.toEquiv, ←Nat.card_congr
      (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F:=F)).toEquiv,
      Theory.SpecificGroups.SymplecticFour.card_sp, hF]
    apply dvd_mul_of_dvd_left
    apply dvd_mul_of_dvd_left
    rw [←pow_mul]
    exact pow_dvd_pow 2 (by omega : 6≤n*4)

/-- Both actual binary rank-two models supply an odd-rank-two witness,
unchanged by the central two-kernel. -/
theorem odd_rank_two_of_model (hZ : IsPGroup 2 (center K)) {n : ℕ} (hn : 1<n)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 (2^n) ∨
      ClassicalGroup.IsPSp (K ⧸ center K) 2 (2^n)) :
    ∃ p, p.Prime ∧ Odd p ∧ 2≤primeRank p K := by
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · obtain ⟨p,hp,ho,hr⟩ := Theory.SpecificGroups.Classical.EvenRankTwoOddRank.linear hn hF
    let : Fact p.Prime := ⟨hp⟩
    refine ⟨p,hp,ho,?_⟩
    rw [←primeRank_quotient_eq_of_isTwoGroup p ho (center K) hZ,primeRank_equiv p e]
    exact hr
  · let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    refine ⟨3,Nat.prime_three,by decide,?_⟩
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (center K) hZ,primeRank_equiv 3 e]
    exact Theory.SpecificGroups.Classical.EvenRankTwoOddRank.symplectic

omit [Finite K] [Finite C] in
/-- The small actual targets have two-part less than 64, while both source models
have a quotient whose order is divisible by 64. -/
theorem not_injective_small_targets {n : ℕ} (hn : 1<n)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 (2^n) ∨
      ClassicalGroup.IsPSp (K ⧸ center K) 2 (2^n))
    (ht : Nonempty (C ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (C ≃* Sporadic.Mathieu.M11) ∨
      Nonempty (C ≃* alternatingGroup (Fin 6)))
    (f : K →* C) : ¬Function.Injective f := by
  intro hf
  have hd := (sixty_four_dvd_card_of_model hn hm).trans (Subgroup.card_dvd_of_injective f hf)
  rcases ht with ht | ht | ht
  · obtain ⟨e⟩ := ht
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3Three.card_PSL] at hd
    norm_num at hd
  · obtain ⟨e⟩ := ht
    rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m11_order] at hd
    norm_num at hd
  · obtain ⟨e⟩ := ht
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at hd
    norm_num at hd

private theorem prime_linear_rank {F : Type*} [Field F] [Finite F]
    (hp : (Nat.card F).Prime) (hlarge : 3<Nat.card F)
    (p : ℕ) [Fact p.Prime] (ho : Odd p) : primeRank p PSL(2,F) ≤ 1 := by
  let : Fact (3<Nat.card F) := ⟨hlarge⟩
  let P : Sylow p PSL(2,F) := default
  exact P.primeRank_le_one_of_isCyclic
    (GorensteinWalter.PSL2Cover.odd_sylow_cyclic_of_card_prime F hp p
      (by intro h; subst p; norm_num at ho) P)

omit [Finite C] in
/-- A prime-field PSL₂ has cyclic odd Sylow subgroups, incompatible with the
actual odd-rank-two witness in the source central quotient. -/
theorem not_injective_prime_linear (hZ : IsPGroup 2 (center K)) {n : ℕ} (hn : 1<n)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 (2^n) ∨
      ClassicalGroup.IsPSp (K ⧸ center K) 2 (2^n))
    {q : ℕ} (hq : q.Prime) (hql : 3<q) (ht : ClassicalGroup.IsPSL C 2 q)
    (f : K →* C) : ¬Function.Injective f := by
  intro hf
  obtain ⟨p,hp,ho,hr⟩ := odd_rank_two_of_model hZ hn hm
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := ht
  have hb := prime_linear_rank (hF ▸ hq) (hF ▸ hql) p ho
  have hle := Theory.GroupTheory.primeRank_le_of_injective p (e.toMonoidHom.comp f) (e.injective.comp hf)
  omega

private theorem rank_of_card_168 {D : Type*} [Group D] [Finite D]
    (hc : Nat.card D=168) (p : ℕ) [Fact p.Prime] (ho : Odd p) : primeRank p D≤1 := by
  let P : Sylow p D := default
  apply P.primeRank_le_one_of_isCyclic
  obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
  have hd : p^n ∣ 168 := by simpa only [hn,hc] using P.card_subgroup_dvd_card
  have hle : n≤1 := by
    by_contra hle
    have hp2 : p^2 ∣ 168 := (pow_dvd_pow p (by omega : 2≤n)).trans hd
    have hp1 : p ∣ 2^3*(3*7) := (dvd_pow_self p (by decide : 2≠0)).trans hp2
    have hpv : p=2 ∨ p=3 ∨ p=7 := by
      rcases (Fact.out : p.Prime).dvd_mul.mp hp1 with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
          ((Fact.out : p.Prime).dvd_of_dvd_pow h))
      rcases (Fact.out : p.Prime).dvd_mul.mp h with h|h
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp h))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq Fact.out (by decide : Nat.Prime 7)).mp h))
    rcases hpv with h|h|h <;> subst p <;> norm_num at *
  exact isCyclic_of_card_dvd_prime (p:=p) (hn ▸ (by simpa using pow_dvd_pow p hle))

/-- The binary degree-three central cover target has odd ranks at most one:
its literal quotient has order 168, and its center is a two-group. -/
theorem not_injective_binary_linear_cover (hZ : IsPGroup 2 (center K))
    (hZC : IsPGroup 2 (center C)) {n : ℕ} (hn : 1<n)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) 3 (2^n) ∨
      ClassicalGroup.IsPSp (K ⧸ center K) 2 (2^n))
    (ht : ClassicalGroup.IsPSL (C ⧸ center C) 3 2)
    (f : K →* C) : ¬Function.Injective f := by
  intro hf
  obtain ⟨p,hp,ho,hr⟩ := odd_rank_two_of_model hZ hn hm
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := ht
  have hc : Nat.card (C ⧸ center C)=168 := by
    rw [Nat.card_congr e.toEquiv]
    have hh := Atlas.ExceptionalSupport.card_psl_mul (F:=F) 3
    norm_num [hF,Fin.prod_univ_succ] at hh
    exact hh
  have hb : primeRank p C ≤ 1 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup p ho (center C) hZC]
    exact rank_of_card_168 hc p ho
  have hle := Theory.GroupTheory.primeRank_le_of_injective p f hf
  omega
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement
