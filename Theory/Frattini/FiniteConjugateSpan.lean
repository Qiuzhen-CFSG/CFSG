module
public import Theory.Frattini.ConjugateSpan

/-!
# Frattini bounds inside a finite conjugate span

An elementary two-subgroup generates a finite two-group under conjugation.
Every square in the span lies in its derived subgroup, so any bound on the
latter bounds its Frattini subgroup. Only the span must be finite; the ambient
group may be an infinite amalgam. This is the paired-orbit estimate in
Meierfrankenfeld--Stellmacher (1993), (3.6), printed p.871.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

theorem finite_conjugateSpan_frattini_le
    (Y H D : Subgroup G) [Finite (conjugateSpanBy Y H)]
    [IsElementaryAbelian 2 Y]
    (hp : IsPGroup 2 (conjugateSpanBy Y H))
    (hc : ⁅conjugateSpanBy Y H,conjugateSpanBy Y H⁆ ≤ D) :
    (frattini (conjugateSpanBy Y H)).map (conjugateSpanBy Y H).subtype ≤ D := by
  let A := conjugateSpanBy Y H
  have hs : ∀ x ∈ A, x ^ 2 ∈ D := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨h,hh,y,hy,rfl⟩ := hx
      rw [conj_pow,elemPow_eq_one_of_isElementaryAbelian y hy,mul_one,mul_inv_cancel]
      exact D.one_mem
    | one => simp
    | inv x _ ih => simpa only [inv_pow] using D.inv_mem ih
    | mul x y hx hy ihx ihy =>
      have he : (x*y)^2 = x^2*⁅x⁻¹,y⁆*y^2 := by
        simp [commutatorElement_def,pow_two,mul_assoc]
      rw [he]
      exact D.mul_mem (D.mul_mem ihx (hc (commutator_mem_commutator (A.inv_mem hx) hy))) ihy
  rw [map_le_iff_le_comap,hp.frattini_eq_closure_squares]
  apply (closure_le _).mpr
  rintro x ⟨y,rfl⟩
  exact hs y y.property
end Subgroup
