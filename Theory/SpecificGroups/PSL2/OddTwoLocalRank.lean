module

public import GorensteinWalter.Section4.PSL2ReflectedTorusCard
public import GorensteinWalter.DihedralOddRotationCentralizer
public import Theory.SpecificGroups.PSL2.OddAutomorphismRank
public import Theory.GroupTheory.TwoLocalRankOfCentralizers

/-!
# Odd-prime two-local ranks in odd-field PSL₂

An involution centralizer is a cyclic torus extended by inversion. Every
odd-prime subgroup lies in the torus, since the other coset consists of
involutions. Thus these centralizers have odd-prime rank at most one.
The elementary normalizer reduction then gives two-local rank at most two.
Source: Huppert II.8.3–4; Aschbacher–Smith A.2.12, printed p.36.
-/

public section
open Subgroup GorensteinWalter Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.PSL2
variable {F : Type*} [Field F] [Finite F]

/-- Every odd-prime subgroup of an involution centralizer lies in its cyclic torus. -/
theorem odd_involution_centralizer_primeRank_le_one
    (hF : IsOddPrimePower (Nat.card F)) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (t : PSL(2,F)) (ht : orderOf t = 2) :
    primeRank p (centralizer ({t} : Set PSL(2,F))) ≤ 1 := by
  have htI : IsInvolution t := ⟨by intro h; simp [h] at ht,
    by simpa only [ht] using pow_orderOf_eq_one t⟩
  obtain ⟨T,s,hT,_,hs,hsT,hinv,hC,_,_⟩ := psl2_reflected_torus_card hF htI
  let C := centralizer ({t} : Set PSL(2,F))
  let P : Sylow p C := Classical.choice inferInstance
  have hss : s * s = 1 := by simpa only [pow_two] using hs.2
  have hle (x : P) : ((x : C) : PSL(2,F)) ∈ T := by
    have hxC : ((x : C) : PSL(2,F)) ∈ T ⊔ zpowers s := hC ▸ (x : C).property
    obtain ⟨u,hu,hx | hx⟩ :=
      (mem_sup_zpowers_of_involution_inverts hsT hss hinv).mp hxC
    · simpa only [hx] using hu
    · have hsq : (((x : C) : PSL(2,F))) ^ 2 = 1 := by
        rw [hx]
        calc
          (u * s) ^ 2 = u * (s * u * s⁻¹) * (s * s) := by rw [pow_two]; group
          _ = 1 := by rw [hinv u hu,hss]; simp
      obtain ⟨k,hk⟩ := P.isPGroup' x
      have hpw : (((x : C) : PSL(2,F))) ^ (p ^ k) = 1 := by
        exact congrArg (fun y : P => ((y : C) : PSL(2,F))) hk
      have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hsq)
        (orderOf_dvd_of_pow_eq_one hpw)
      rw [(Nat.coprime_two_left.mpr (ho.pow)).gcd_eq_one] at hd
      have hxone : ((x : C) : PSL(2,F)) = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
      rw [hxone]
      exact T.one_mem
  let f : P →* T := (C.subtype.comp (P : Subgroup C).subtype).codRestrict T hle
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : T => (y : PSL(2,F))) h
  let : IsCyclic T := hT
  exact P.primeRank_le_one_of_isCyclic (isCyclic_of_injective f hf)

/-- Every odd prime has two-local rank at most two in the actual odd-field PSL₂. -/
theorem odd_twoLocalPrimeRank_le_two
    (hF : IsOddPrimePower (Nat.card F)) {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    twoLocalPrimeRank p PSL(2,F) ≤ 2 := by
  let : Finite PGL(2,F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hr : primeRank 2 PSL(2,F) ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 2 Matrix.ProjectiveSpecialLinearGroup.toPGL
      Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).trans (odd_pgl_two_rank F hF)
  have hi := odd_involution_centralizer_primeRank_le_one hF ho
  have hf (E : Subgroup PSL(2,F)) (_hE : IsElementaryAbelian 2 E) (hc : Nat.card E = 4) :
      primeRank p (centralizer (E : Set PSL(2,F))) ≤ 1 := by
    obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [hc]; decide)
    have htG : orderOf (t : PSL(2,F)) = 2 := (orderOf_coe t).trans ht
    have hle : centralizer (E : Set PSL(2,F)) ≤
        centralizer ({(t : PSL(2,F))} : Set PSL(2,F)) :=
      centralizer_le (Set.singleton_subset_iff.mpr t.property)
    exact (primeRank_mono p hle).trans (hi t htG)
  simpa using twoLocalPrimeRank_le_max_of_centralizers ho hr hi hf
end Theory.PSL2
