module
public import Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers.NormalForms
public import Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual.Standard
public import Theory.SpecificGroups.SymplecticFour.RootSubgroup.ElementCentralizer
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.Coordinates

/-!
# Symplectic transvections are not squares

An element centralizing a long-root transvection fixes its moved vector.
If its square were that transvection, form preservation on a hyperbolic
partner and its image would force the root parameter to vanish. Normal
forms transfer this to every literal rank-one involution. This is the
square obstruction used to exclude the Suzuki row in the rank-one
normalizer inspection of Aschbacher--Smith G.4.1, printed p.342.
-/

public noncomputable section
open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour
open InvolutionTypes InvolutionCentralizers RootNormalizerResidual
variable {F:Type*} [Field F] [CharP F 2]
local notation "a" => (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "c" => (Sum.inr (0 : Fin 2) : Fin 2 ⊕ Fin 2)
private theorem root_zero_ne_square {s:F} (hs:s≠0) (x:Sp F) :
    x^2≠rootElement 0 s := by
  intro hx
  have hc : Commute x (rootElement 0 s) := by
    rw [←hx]
    exact Commute.self_pow x 2
  have hC : x∈centralizer (RootSubgroup.group (F:=F) 0:Set (Sp F)) := by
    apply mem_centralizer_iff.mpr
    intro y hy
    obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff 0 y).mp hy
    exact (RootSubgroup.commute_element_of_ne_zero 0 hs x hc t).symm.eq
  rw [centralizer_zero_eq] at hC
  have hfix := (mem_pointLocal_iff_fixed x).mp hC
  let v : Vector F := Pi.single c 1
  have hsqv : x•(x•v)=v+s•e 0 := by
    rw [←mul_smul,←pow_two,hx]
    ext i
    rcases i with i|i <;> fin_cases i <;>
      simp [rootElement,rootMatrix,Matrix.mulVec, dotProduct,
        Fintype.sum_sum_type,Fin.sum_univ_two,v,e,Matrix.single_apply]
  have hve : form F (x•v) (e 0)=1 := by
    rw [←hfix,preserves_form]
    simp [form_apply,v,e,Fin.sum_univ_two,CharTwo.neg_eq]
  have hsym : form F (x•v) v=form F v (x•v) := by
    simp [form_apply,v,Fin.sum_univ_two,CharTwo.neg_eq]
  have hb := preserves_form x v (x•v)
  rw [hsqv] at hb
  simp only [map_add,LinearMap.map_smul,smul_eq_mul,hve,mul_one,hsym] at hb
  exact hs (by linear_combination hb)

/-- A literal rank-one symplectic involution is not a square. -/
theorem isB1_not_square [Finite F] (t:Sp F) (ht:IsB1 t) (x:Sp F) : x^2≠t := by
  intro hx
  obtain ⟨h,s,hs,he⟩ := isB1_conjugate_root0 t ht
  apply root_zero_ne_square hs (h⁻¹*x*h)
  calc
    (h⁻¹*x*h)^2=h⁻¹*x^2*h := by simp [pow_two,mul_assoc]
    _ = rootElement 0 s := by rw [hx,he]; simp [mul_assoc]
end Theory.SpecificGroups.SymplecticFour
