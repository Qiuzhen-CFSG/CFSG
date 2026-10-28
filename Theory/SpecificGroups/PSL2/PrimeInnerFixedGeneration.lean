module
public import Theory.SpecificGroups.PSL2.PrimeInvolutionCentralizerMaximal
public import Theory.SpecificGroups.PSL2.AdjacentPowerOddCore
public import Theory.SpecificGroups.PSL2.PrimeOuterFixed
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import Theory.GroupTheory.DihedralGeneratedFactor
public import Theory.GroupTheory.SpecificGroups.CyclicInvertedDihedral
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Fixed generation from an inner involution in prime PSL₂

For an adjacent-power prime greater than nine, an involution centralizer is
a maximal dihedral two-group with center of order two. Consequently, the
fixed subgroups of two distinct involutory automorphisms generate PSL₂ as
soon as one of the automorphisms is conjugation by an involution.

An outer involution has a fixed dihedral group with nontrivial odd rotation
subgroup, so its fixed subgroup cannot lie in this two-centralizer. Two inner
involutions with the same centralizer are equal: each is its unique central
involution. These facts close the large-prime case of the crossed-dihedral
fixed-generation argument in Aschbacher–Smith, Lemma 2.5.21, printed p.566.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

private theorem adjacent_centralizer_center_card {p k : ℕ} [Fact p.Prime]
    (hp : 9 < p) (hpk : p-1=2^k ∨ p+1=2^k)
    (t : PSL(2,ZMod p)) (ht : orderOf t=2) :
    Nat.card (center (centralizer ({t} : Set PSL(2,ZMod p))))=2 := by
  have ho : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  let hF : IsOddPrimePower (Nat.card (ZMod p)) := ⟨p,1,Fact.out,ho,by decide,by simp⟩
  have ht' : IsInvolution t := (orderOf_eq_prime_iff.mp ht).symm
  let D := centralizer ({t} : Set PSL(2,ZMod p))
  have hD : IsPGroup 2 D := involutionCentralizer_isTwoGroup_of_adjacent_power
    hF (by simpa using (show 3<p by omega)) (by simpa using hpk) t ht
  obtain ⟨R,w,hR,_,hw,hwR,hinv,hEq,_,_⟩ := psl2_reflected_torus_card hF ht'
  have hRD : R ≤ D := by rw [show D=R ⊔ zpowers w from hEq]; exact le_sup_left
  have hRtwo : IsPGroup 2 R := hD.of_injective (inclusion hRD) (inclusion_injective _)
  obtain ⟨m,hm⟩ := hRtwo.exists_card_eq
  obtain ⟨e₀⟩ := nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted R w hR hw.2 hwR hinv
  let e : D ≃* DihedralGroup (2^m) := by
    rw [← hm]
    exact (MulEquiv.subgroupCongr hEq).trans e₀
  have hm2 : 2 ≤ m := by
    have hc : Nat.card D = 2 * 2^m := by
      rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
    have hlow : p-1 ≤ Nat.card D := by
      rcases involution_centralizer_card_cases hF t ht' with he | he <;>
        simp only [Nat.card_zmod] at he <;> dsimp only [D] <;> omega
    by_contra! hh
    interval_cases m <;> norm_num at hc <;> omega
  exact DihedralGroup.center_card_of_equiv hm2 e

private theorem involution_eq_of_same_adjacent_centralizer
    {p k : ℕ} [Fact p.Prime] (hp : 9<p) (hpk : p-1=2^k ∨ p+1=2^k)
    (x t : PSL(2,ZMod p)) (hx : orderOf x=2) (ht : orderOf t=2)
    (he : centralizer ({x} : Set PSL(2,ZMod p)) = centralizer ({t} : Set PSL(2,ZMod p))) : x=t := by
  let D := centralizer ({t} : Set PSL(2,ZMod p))
  have htD : t∈D := mem_centralizer_singleton_iff.mpr rfl
  have hxD : x∈D := by
    change x ∈ centralizer ({t} : Set PSL(2,ZMod p))
    rw [← he]
    exact mem_centralizer_singleton_iff.mpr rfl
  let tD : D := ⟨t,htD⟩
  let xD : D := ⟨x,hxD⟩
  have htZ : tD∈center D := mem_center_iff.mpr fun d =>
    Subtype.ext (mem_centralizer_singleton_iff.mp d.property)
  have hxZ : xD∈center D := mem_center_iff.mpr fun d =>
    Subtype.ext (mem_centralizer_singleton_iff.mp (he.symm ▸ d.property))
  obtain ⟨z,hz,hunique⟩ := (Nat.card_eq_two_iff' (1 : center D)).mp
    (adjacent_centralizer_center_card hp hpk t ht)
  have hxZne : (⟨xD,hxZ⟩ : center D) ≠ 1 := by
    intro he
    exact (orderOf_eq_prime_iff.mp hx).2
      (congrArg (fun a : center D => a.val.val) he)
  have htZne : (⟨tD,htZ⟩ : center D) ≠ 1 := by
    intro he
    exact (orderOf_eq_prime_iff.mp ht).2
      (congrArg (fun a : center D => a.val.val) he)
  have hxt : (⟨xD,hxZ⟩ : center D) = ⟨tD,htZ⟩ :=
    (hunique _ hxZne).trans (hunique _ htZne).symm
  exact congrArg (fun a : center D => a.val.val) hxt

/-- Two distinct acting involutions, one inner, generate through their fixed
groups for the larger adjacent-power primes. -/
theorem prime_fixed_generation_of_inner_involution
    {p k : ℕ} [Fact p.Prime] (hp : 9<p) (hpk : p-1=2^k ∨ p+1=2^k)
    (α β : MulAut PSL(2,ZMod p)) (hβ : β^2=1) (hne : β≠α)
    (t : PSL(2,ZMod p)) (ht : orderOf t=2) (hα : α=MulAut.conj t)
    (N : Subgroup PSL(2,ZMod p)) (hfixα : α.fixedSubgroup≤N)
    (hfixβ : β.fixedSubgroup≤N) : N=⊤ := by
  have ho : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  let hF : IsOddPrimePower (Nat.card (ZMod p)) := ⟨p,1,Fact.out,ho,by decide,by simp⟩
  let D := centralizer ({t} : Set PSL(2,ZMod p))
  have hαD : α.fixedSubgroup=D := by
    rw [hα]
    ext x
    rw [MulAut.mem_fixedSubgroup]
    change t*x*t⁻¹=x ↔ _
    exact ⟨fun h => mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp h).symm, fun h =>
        mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp h).symm⟩
  have hDle : D≤N := hαD ▸ hfixα
  by_contra hn
  have hmax := prime_involution_centralizer_isCoatom_of_nine_lt ho (by simp) hp t
    (orderOf_eq_prime_iff.mp ht).symm
  have hND : N=D := le_antisymm
    ((isCoatom_iff_ge_of_le.mp hmax).2 N hn hDle) hDle
  have hDtwo : IsPGroup 2 D := involutionCentralizer_isTwoGroup_of_adjacent_power hF
    (by simpa using (show 3<p by omega)) (by simpa using hpk) t ht
  have hβD : β.fixedSubgroup≤D := hND ▸ hfixβ
  have hinner : β∈(MulAut.conj : PSL(2,ZMod p) →* MulAut PSL(2,ZMod p)).range := by
    by_contra hout
    obtain ⟨n,hnodd,hnlarge,⟨e⟩⟩ := prime_outer_fixed_dihedral (by omega : 3<p)
      (MulEquiv.refl PSL(2,ZMod p)) β hβ hout
    have htwo := hDtwo.of_injective (inclusion hβD) (inclusion_injective _)
    obtain ⟨a,ha⟩ := htwo.exists_card_eq
    have hncard : Nat.card β.fixedSubgroup=2*n := by
      rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
    have hd : n∣2^a := by rw [←ha,hncard]; exact dvd_mul_left _ _
    have hcop : n.Coprime (2^a) := (Nat.coprime_two_right.mpr hnodd).pow_right a
    have he : n=1 := hcop.eq_one_of_dvd hd
    omega
  obtain ⟨x,hx⟩ := hinner
  have hβne : β≠1 := by
    intro he
    apply hn
    apply top_unique
    intro g _
    apply hfixβ
    rw [he,MulAut.mem_fixedSubgroup]
    rfl
  have hx2 : x^2=1 := by
    apply MulAut.conj_injective_of_center_eq_bot (psl2_center_eq_bot (ZMod p))
    rw [map_pow,hx,hβ,map_one]
  have hxne : x≠1 := by intro he; apply hβne; rw [←hx,he,map_one]
  have hxo : orderOf x=2 := orderOf_eq_prime hx2 hxne
  have hCx : centralizer ({x} : Set PSL(2,ZMod p))≤D := by
    intro g hg
    apply hβD
    rw [←hx,MulAut.mem_fixedSubgroup]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hg).symm
  have hcard : Nat.card (centralizer ({x} : Set PSL(2,ZMod p)))=Nat.card D := by
    obtain ⟨g,hg⟩ := isConj_iff.mp (involutions_isConj x t hxo ht)
    have he : (MulAut.conj g) x = t := hg
    change Nat.card (centralizer ({x} : Set PSL(2,ZMod p))) =
      Nat.card (centralizer ({t} : Set PSL(2,ZMod p)))
    rw [← he]
    exact Nat.card_congr
      (Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv
        (MulAut.conj g) x).toEquiv
  have he := eq_of_le_of_card_ge hCx hcard.ge
  have hxt := involution_eq_of_same_adjacent_centralizer hp hpk x t hxo ht he
  exact hne (hx.symm.trans (by rw [hxt,←hα]))

end Theory.PSL2
