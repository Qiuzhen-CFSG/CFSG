module
public import Theory.SpecificGroups.SymmetricFourWreath.LocalStructure.Coordinates

/-!
# The three factor types used in the wreath involution classes

Identity, a transposition, and a double transposition represent the three
square-one types in S4. The type is conjugacy invariant because conjugation
preserves identity and existence of a fixed point. Only the 24-element
representative selection is checked by a finite kernel certificate.

Source: Aschbacher–Smith 13.9.3–4, printed p.970.
-/

@[expose] public section
namespace SymmetricFourWreath.InvolutionClasses
open Subgroup

def kind (a : S4) : Fin 3 := if a=1 then 0 else if ∃i,a i=i then 1 else 2

def factorRepresentative (i : Fin 3) : S4 :=
  if i=0 then 1 else if i=1 then square (DihedralGroup.sr 0) else square (DihedralGroup.r 2)

theorem kind_conjugate (g a : S4) : kind (g*a*g⁻¹)=kind a := by
  have hone : g*a*g⁻¹=1 ↔ a=1 := by
    constructor
    · intro h
      have hh := congrArg (fun x:S4=>g⁻¹*x*g) h
      simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,mul_one,inv_mul_cancel] using hh
    · rintro rfl
      simp
  have hfix : (∃i,(g*a*g⁻¹) i=i) ↔ ∃i,a i=i := by
    constructor
    · rintro ⟨i,hi⟩
      refine ⟨g⁻¹ i,?_⟩
      apply g.injective
      simpa only [Equiv.Perm.mul_apply,Equiv.Perm.inv_def,Equiv.apply_symm_apply] using hi
    · rintro ⟨i,hi⟩
      refine ⟨g i,?_⟩
      simp only [Equiv.Perm.mul_apply,Equiv.Perm.inv_def,Equiv.symm_apply_apply,hi]
  simp only [kind,hone,hfix]


theorem factor_involution_representative : ∀a:S4,a*a=1 →
    ∃g:S4,g*a*g⁻¹=factorRepresentative (kind a) := by decide +kernel

theorem factor_representative_kind : ∀i:Fin 3,kind (factorRepresentative i)=i := by decide +kernel

theorem factor_representative_mem_plane : ∀i:Fin 3,
    ∃a∈plane false,square a=factorRepresentative i := by decide +kernel

end SymmetricFourWreath.InvolutionClasses
