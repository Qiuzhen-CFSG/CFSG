module
public import Theory.GroupTheory.InvolutionOrbitCentralizerSupplement
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Involution centralizers over a normal cyclic section

The involution of a normal cyclic section is fixed by every ambient
conjugation. Transitivity of the core on its involution lifts therefore
makes the involution centralizer supplement the core. Unlike an abelian
ambient quotient, only the marked intermediate section must be cyclic.

Used for Aschbacher–Smith 2.4.23(4), printed p.537.
-/
public section
open Subgroup
namespace Subgroup
variable {P : Type*} [Group P] [Finite P]

theorem conjugate_involution_mul_inv_mem_of_normal_cyclic_section
    (R S : Subgroup P) [R.Normal] [S.Normal]
    [IsCyclic (S ⧸ R.subgroupOf S)]
    (s : P) (hsS : s ∈ S) (hs : orderOf s = 2) (hsR : s ∉ R) (g : P) :
    (g * s * g⁻¹) * s⁻¹ ∈ R := by
  let v : S := ⟨g * s * g⁻¹, (inferInstance : S.Normal).conj_mem s hsS g⟩
  let sS : S := ⟨s,hsS⟩
  let q : S →* S ⧸ R.subgroupOf S := QuotientGroup.mk' _
  have hord (a : S) (ha : orderOf (a : P) = 2) (hne : (a : P) ∉ R) :
      orderOf (q a) = 2 := by
    apply orderOf_eq_prime
    · rw [←map_pow]
      have he : a ^ 2 = 1 := Subtype.ext (by simpa only [Subgroup.coe_pow,Subgroup.coe_one,ha] using pow_orderOf_eq_one (a : P))
      rw [he,map_one]
    · exact fun he => hne ((QuotientGroup.eq_one_iff a).mp he)
  have hv : orderOf (v : P) = 2 := ((MulAut.conj g).orderOf_eq s).trans hs
  have hn : (v : P) ∉ R := by
    intro he
    have hh := (inferInstance : R.Normal).conj_mem (g*s*g⁻¹) he g⁻¹
    exact hsR (by simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_inv_cancel,mul_one] using hh)
  have he : q v = q sS := IsCyclic.eq_of_orderOf_eq_two (hord v hv hn) (hord sS hs hsR)
  have hm : v * sS⁻¹ ∈ R.subgroupOf S := (QuotientGroup.eq_one_iff _).mp (by
    change q (v*sS⁻¹)=1
    rw [map_mul,map_inv,he,mul_inv_cancel])
  exact hm

/-- The literal involution orbit supplements the core when the marked
intermediate quotient is normal cyclic. -/
theorem sup_centralizer_eq_top_of_normal_cyclic_section
    (R S : Subgroup P) [R.Normal] [S.Normal]
    [IsCyclic (S ⧸ R.subgroupOf S)]
    (s : P) (hsS : s ∈ S) (hs : orderOf s = 2) (hsR : s ∉ R)
    (horbit : ∀ v : P, orderOf v = 2 → v * s⁻¹ ∈ R →
      ∃ r ∈ R, r * s * r⁻¹ = v) : R ⊔ centralizer ({s} : Set P) = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨r,hr,he⟩ := horbit (g*s*g⁻¹) (((MulAut.conj g).orderOf_eq s).trans hs)
    (conjugate_involution_mul_inv_mem_of_normal_cyclic_section R S s hsS hs hsR g)
  have hc : r⁻¹*g ∈ centralizer ({s} : Set P) := by
    apply mem_centralizer_singleton_iff.mpr
    have he' := congrArg (fun x => r⁻¹*x*g) he
    simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using he'.symm
  have hh := (R ⊔ centralizer ({s} : Set P)).mul_mem (mem_sup_left hr) (mem_sup_right hc)
  simpa only [←mul_assoc,mul_inv_cancel,one_mul] using hh
end Subgroup
