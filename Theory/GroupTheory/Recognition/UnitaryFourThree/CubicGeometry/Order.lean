module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.QuotientSylow
public import Theory.GroupTheory.SylowTrivialIntersectionCount

/-!
# Order of the original faithful cubic-kernel normalizer quotient

The actual TI Sylow-nine subgroup acts freely on the other Sylows, so their
number is one modulo9. Its normalizer has order36. The faithful GL₄(3)
embedding, Sylow-two order8 and Sylow-three order9 leave only the possible
orders72 times a divisor of65; the stronger congruence selects360.
No group is recognized from its order here. This is precisely the arithmetic
step before the independent A₆ recognition in Aschbacher45.9,printed p247.
-/

public section
private theorem cubic_ti_order_arithmetic (n k:ℕ)
    (hdiv:n∣24261120) (h8:8∣n) (h9:9∣n) (h16:¬16∣n) (h27:¬27∣n)
    (hnk:n=36*k) (hcong:9∣k-1) : n=360 := by
  have h72:72∣n:=(by decide:Nat.Coprime 8 9).mul_dvd_of_dvd_of_dvd h8 h9
  obtain ⟨a,ha⟩:=h72
  have ha2:¬2∣a:=by
    rintro ⟨b,hb⟩
    apply h16
    rw [ha,hb]
    exact ⟨9*b,by ring⟩
  have ha3:¬3∣a:=by
    rintro ⟨b,hb⟩
    apply h27
    rw [ha,hb]
    exact ⟨8*b,by ring⟩
  have hac:Nat.Coprime a 5184:=by
    change Nat.Coprime a (2^6*3^4)
    exact ((Nat.prime_two.coprime_iff_not_dvd.mpr ha2).symm.pow_right 6).mul_right
      ((Nat.prime_three.coprime_iff_not_dvd.mpr ha3).symm.pow_right 4)
  have had:a∣5184*65:=by
    apply (Nat.mul_dvd_mul_iff_left (by decide:0<72)).mp
    simpa only [←ha] using hdiv
  have ha65:a∣65:=hac.dvd_of_dvd_mul_left had
  have hh:=Nat.mem_divisors.mpr ⟨ha65,(by decide:65≠0)⟩
  have hd:Nat.divisors 65={1,5,13,65}:=by decide
  simp only [hd,Finset.mem_insert,Finset.mem_singleton] at hh
  rcases hh with hh|hh|hh|hh <;> omega

open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G:Type*} [Group G] [Finite G] {z:G} {h:IsType z} {P:Sylow 3 (centralizer z)}
variable (c:SourceConfiguration h P)

theorem quotient_card_mul_kernel :
    Nat.card (normalizer (c.toSourceData.V:Set G))=
      Nat.card (NormalizerAction.Star c.toSourceData.V)*81 := by
  let V:=c.toSourceData.V
  have hc:Nat.card (NormalizerAction.C V)=81:=by
    change Nat.card ((Subgroup.centralizer (V:Set G)).subgroupOf (normalizer (V:Set G)))=81
    rw [h.cubic_kernel_centralizer P,Nat.card_congr (subgroupOfEquivOfLe V.le_normalizer).toEquiv]
    exact c.kernel_card
  have hh:=card_eq_card_quotient_mul_card_subgroup (NormalizerAction.C V)
  rw [hc] at hh
  exact hh

theorem quotient_card : Nat.card (NormalizerAction.Star c.toSourceData.V)=360 := by
  let V:=c.toSourceData.V
  let M:=normalizer (V:Set G)
  let B:=NormalizerAction.Star V
  let S:=c.quotientSylow
  have hMul:Nat.card M=Nat.card B*81:=c.quotient_card_mul_kernel
  have hdiv:Nat.card B∣24261120:=by
    have hh:=h.cubic_kernel_normalizer_index_dvd P
    change (V.subgroupOf M).index∣24261120 at hh
    change (NormalizerAction.C V).index∣24261120
    change ((Subgroup.centralizer (V:Set G)).subgroupOf M).index∣24261120
    rwa [h.cubic_kernel_centralizer P]
  have h8:8∣Nat.card B:=by
    obtain ⟨T,hT⟩:=h.cubic_kernel_sylow_two P
    have hd:=T.toSubgroup.card_subgroup_dvd_card
    rw [hT,hMul] at hd
    omega
  have h9:9∣Nat.card B:=c.quotientSylow_card ▸ S.toSubgroup.card_subgroup_dvd_card
  have h16:¬16∣Nat.card B:=fun hd=>h.cubic_kernel_normalizer_not_sixteen P
    (hMul ▸ dvd_mul_of_dvd_left hd 81)
  have h27:¬27∣Nat.card B:=by
    have hh:=S.toSubgroup.card_mul_index
    rw [c.quotientSylow_card] at hh
    intro hd
    have h3:3∣S.toSubgroup.index:=by
      apply (Nat.mul_dvd_mul_iff_left (by decide:0<9)).mp
      simpa only [hh] using hd
    exact S.not_dvd_index h3
  have hnk:Nat.card B=36*Nat.card (Sylow 3 B):=by
    have hh:=(normalizer (S:Set B)).card_mul_index
    rw [c.quotientSylow_normalizer_card,←S.card_eq_index_normalizer] at hh
    exact hh.symm
  have hcong:9∣Nat.card (Sylow 3 B)-1:=by
    have hh:=S.card_dvd_card_sub_one_of_ti c.quotientSylow_Ti
    rwa [c.quotientSylow_card] at hh
  exact cubic_ti_order_arithmetic (Nat.card B) (Nat.card (Sylow 3 B)) hdiv h8 h9 h16 h27 hnk hcong
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
