module
public import Theory.GroupTheory.CubicCentralSquareExtension
public import Theory.GroupTheory.PrimeOrderLift

/-!
# Generation above a two-core with quotient of order six

An element of order three survives a two-group kernel.  An element whose square lies in the kernel and which inverts
it also survives, so their images generate a quotient of order six.  Together
with the core they therefore generate the original group.  The application is
the original nonabelian order-96 vertex in Aschbacher–Smith F.1.12(I)(8).
-/

public section
open Subgroup
namespace CubicCentralSquareExtension
variable {A G:Type*} [Group A] [Group G] [Finite G]

theorem generated_eq_top_of_six_quotient (N:Subgroup G) [N.Normal]
    (f:A→*G) (hf:f.range=N) (c b:G) (hc:orderOf c=3)
    (hb:b^2∈N) (hinv:b*c*b⁻¹=c⁻¹) (hN:IsPGroup 2 N)
    (hcard:Nat.card (G⧸N)=6) : generated f c b=⊤ := by
  let q:=QuotientGroup.mk' N
  have hcq:orderOf (q c)=3 := by
    have hk:IsPGroup 2 q.ker:=by
      change IsPGroup 2 (QuotientGroup.mk' N).ker
      rw [QuotientGroup.ker_mk']
      exact hN
    exact (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hk c (by rw [hc]; decide)).trans hc
  have hbi:q b≠1 := by
    intro he
    have hh:=congrArg q hinv
    simp only [map_mul,map_inv,he,one_mul,inv_one,mul_one] at hh
    have ht:(q c)^2=1 := by
      rw [pow_two]
      nth_rw 1 [hh]
      exact inv_mul_cancel _
    have hd:=orderOf_dvd_of_pow_eq_one ht
    rw [hcq] at hd
    norm_num at hd
  have hbq:orderOf (q b)=2 := by
    let _ : Fact (Nat.Prime 2):=⟨by decide⟩
    apply orderOf_eq_prime
    · rw [←map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hb
    · exact hbi
  let J:Subgroup (G⧸N):=(generated f c b).map q
  have hcJ:q c∈J:=mem_map_of_mem q (subset_closure (Or.inr (Or.inl rfl)))
  have hbJ:q b∈J:=mem_map_of_mem q (subset_closure (Or.inl rfl))
  have h3:3∣Nat.card J := by
    have h:=orderOf_dvd_natCard (⟨q c,hcJ⟩:J)
    rwa [←Subgroup.orderOf_coe,hcq] at h
  have h2:2∣Nat.card J := by
    have h:=orderOf_dvd_natCard (⟨q b,hbJ⟩:J)
    rwa [←Subgroup.orderOf_coe,hbq] at h
  have hJ:J=⊤ := by
    apply Subgroup.eq_of_le_of_card_ge le_top
    rw [card_top,hcard]
    have hd:=Nat.lcm_dvd h2 h3
    norm_num at hd
    exact Nat.le_of_dvd Nat.card_pos hd
  have hsup:generated f c b⊔N=⊤ := by
    have h:=congrArg (comap q) hJ
    simpa only [J,comap_map_eq,comap_top,q,QuotientGroup.ker_mk'] using h
  have hn:N≤generated f c b := by
    rw [←hf]
    rintro _ ⟨a,rfl⟩
    exact subset_closure (Or.inr (Or.inr ⟨a,rfl⟩))
  rwa [sup_eq_left.mpr hn] at hsup
end CubicCentralSquareExtension
