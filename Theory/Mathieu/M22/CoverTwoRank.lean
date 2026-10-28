module
public import Theory.Mathieu.M22.UniversalMultiplier.TwoPrimary.Reduction
public import Theory.Mathieu.M22.UniversalMultiplier.TwoPrimary.HexadLifting
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.KernelGeometry
public import Theory.Alternating.PrimeRank
public import Theory.GroupTheory.PrimeRankHom
public import Theory.Quasithin.CoprimeRank

/-!
# Two-rank of full perfect M₂₂ covers

A two-primary central extension contains the genuine lifted A₆ hexad
complement. A nontrivial two-kernel contributes an independent central
involution, giving rank at least three. With odd kernel, the native
hexad elementary sixteen lifts by coprime rank transport. Removing the
cubic Sylow subgroup of the original central kernel reduces every perfect
cover to these cases, without replacing its full group by its quotient.

Source application: Aschbacher--Smith 4.2.13, printed p.612, and A.1.28,
p.26; the native hexad lifting is I.2.2(6), p.412.
-/

public noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped Pointwise
namespace Sporadic.Mathieu.M22CentralCover

private theorem twoPrimary_rank {E : Type*} [Group E] [Finite E]
    (f : Cover E M22) (hp : IsPGroup 2 f.toMonoidHom.ker) :
    3 ≤ primeRank 2 E := by
  by_cases h2 : 2 ∣ Nat.card f.toMonoidHom.ker
  · obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := f.toMonoidHom.ker) 2 h2
    obtain ⟨s,hs⟩ := M22UniversalMultiplier.exists_hexadSection_lift
      f.toMonoidHom f.surjective f.ker_le_center hp m22Hexad123_mem
    have hfs : Function.Injective (f.toMonoidHom.comp s) := by
      rw [hs]
      exact (MulAction.stabilizer M22 m22Hexad123).subtype_injective.comp
        (m22HexadSection_injective m22Hexad123_mem)
    have hsi : Function.Injective s := Function.Injective.of_comp hfs
    have htr : (t : E) ∉ s.range := by
      rintro ⟨a,ha⟩
      have he : a = 1 := hfs (by simpa only [MonoidHom.comp_apply,map_one,ha] using (show f.toMonoidHom (t : E) = 1 from t.property))
      have ht1 : t = 1 := Subtype.ext (by simpa only [ha,he,map_one,coe_one] using ha.symm)
      rw [ht1,orderOf_one] at ht
      omega
    have hr : primeRank 2 s.range = 2 := by
      rw [← primeRank_congr 2 (MonoidHom.ofInjective hsi)]
      exact (GLS3.Chapter5.PRank.alternating_hasPRank_two 6).primeRank_eq Nat.prime_two
    have hle := primeRank_succ_le_sup_zpowers s.range (t : E)
      ((orderOf_coe t).trans ht)
      (fun a _ => mem_centralizer_singleton_iff.mpr
        (mem_center_iff.mp (f.ker_le_center t.property) a)) htr
    rw [hr] at hle
    exact hle.trans (primeRank_le_of_injective 2 _ (s.range ⊔ zpowers (t : E)).subtype_injective)
  · have he := primeRank_eq_of_surjective_of_coprime 2 f.toMonoidHom f.surjective
      (Nat.prime_two.coprime_iff_not_dvd.mpr h2)
    rw [he]
    let : IsElementaryAbelian 2 (m22HexadPointwiseKernel m22Hexad123) :=
      m22HexadPointwiseKernel_elementaryAbelian m22Hexad123_mem
    exact (by decide : 3 ≤ 4).trans (IsElementaryAbelian.primeRank_ge_of_card
      _ (m22HexadPointwiseKernel_card m22Hexad123_mem))

/-- Every finite perfect central cover of the native M₂₂ has two-rank at least three. -/
theorem three_le_twoRank {E : Type*} [Group E] [Finite E]
    (f : Cover E M22) : 3 ≤ primeRank 2 E := by
  let P : Sylow 3 f.toMonoidHom.ker := Classical.choice inferInstance
  let D : Subgroup E := (P : Subgroup f.toMonoidHom.ker).map f.toMonoidHom.ker.subtype
  have hD : D ≤ f.toMonoidHom.ker := map_subtype_le _
  have hDc : D ≤ center E := hD.trans f.ker_le_center
  let : D.Normal := ⟨fun x hx y => by
    rw [mem_center_iff.mp (hDc hx) y,mul_inv_cancel_right]
    exact hx⟩
  let g := f.quotientKernelSubgroup D hD
  have hcardD : Nat.card D = Nat.card P := card_map_of_injective f.toMonoidHom.ker.subtype_injective
  have hgcard : Nat.card g.toMonoidHom.ker = (P : Subgroup f.toMonoidHom.ker).index := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := P))
    rw [←hcardD,←f.card_kernel_quotientKernelSubgroup D hD,hcardD,card_mul_index]
  have hg3 : ¬ 3 ∣ Nat.card g.toMonoidHom.ker := by
    rw [hgcard]
    exact P.not_dvd_index
  have hg2 : IsPGroup 2 g.toMonoidHom.ker := by
    apply (isPGroup_iff_primeFactors_card_subset (by decide : (2 : ℕ) ≠ 0)).mpr
    intro p hp
    obtain ⟨hpprime,hpd,_⟩ := Nat.mem_primeFactors.mp hp
    have heq : p = 2 := by
      by_contra hp2
      by_cases hp3 : p = 3
      · exact hg3 (hp3 ▸ hpd)
      · exact M22UniversalMultiplier.not_dvd_kernel_of_ne_two_three g hpprime hp2 hp3 hpd
    subst p
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two,dvd_rfl,by decide⟩
  have hc : Nat.Coprime 2 (Nat.card D) := by
    rw [hcardD]
    obtain ⟨n,hn⟩ := P.isPGroup'.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_right n
  have he := primeRank_eq_of_surjective_of_coprime 2 (QuotientGroup.mk' D)
    (QuotientGroup.mk'_surjective D) (by simpa only [QuotientGroup.ker_mk'] using hc)
  rw [he]
  exact twoPrimary_rank g hg2
end Sporadic.Mathieu.M22CentralCover
