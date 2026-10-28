module
public import Theory.SpecificGroups.SymmetricFourWreath.InvolutionClasses.Reduction

/-!
# The six involution classes in the symmetric-four wreath product

The two base coordinates have identity, transposition, or double-transposition
type. Their unordered nontrivial pairs give five classes, and the swapping
involutions form the sixth. A conjugacy-invariant index both exhausts and
separates the six literal source representatives. Only the nine possible
factor-type pairs are checked by a finite certificate.

Source: Aschbacher–Smith 13.9.3, printed p.970.
-/

@[expose] public section
namespace SymmetricFourWreath.InvolutionClasses
open Subgroup
private instance : DecidableEq W := (RegularWreathProduct.equivProd S4 C2).injective.decidableEq

def pairIndex (i j : Fin 3) : Fin 6 :=
  if i=0 then (if j=1 then 2 else 1)
  else if j=0 then (if i=1 then 2 else 1)
  else if i=1 then (if j=1 then 3 else 4)
  else if j=1 then 4 else 0

theorem pairIndex_comm : ∀i j:Fin 3,pairIndex i j=pairIndex j i := by decide +kernel

def classIndex (x : W) : Fin 6 :=
  if x.right=1 then pairIndex (kind (x.left 1)) (kind (x.left turn)) else 5

def representative (i : Fin 6) : W :=
  if i=0 then z else if i=1 then t else if i=2 then factor 1 (square (DihedralGroup.sr 0))
  else if i=3 then sylowEmbedding (pair (DihedralGroup.sr 0,DihedralGroup.sr 0))
  else if i=4 then sylowEmbedding (pair (DihedralGroup.sr 0,DihedralGroup.r 2)) else swap

theorem representative_index : ∀i:Fin 6,classIndex (representative i)=i := by decide +kernel

theorem representative_square : ∀i:Fin 6,representative i*representative i=1 := by decide +kernel

theorem representative_ne_one : ∀i:Fin 6,representative i≠1 := by decide +kernel

theorem representative_order (i : Fin 6) : orderOf (representative i)=2 :=
  orderOf_eq_prime (by simpa only [pow_two] using representative_square i) (representative_ne_one i)

theorem classIndex_conjugate (g x : W) : classIndex (g*x*g⁻¹)=classIndex x := by
  have hr : (g*x*g⁻¹).right=x.right := by simp
  rw [classIndex,hr,classIndex]
  by_cases hx:x.right=1
  · simp only [hx,ite_true,conjugate_left g x hx,kind_conjugate]
    rcases c2_eq_one_or_turn g.right with h|h
    · simp only [h,inv_one,one_mul]
    · simp only [h,turn_inv,mul_one,turn_sq,pairIndex_comm]
  · simp only [hx,ite_false]

def baseForm (i j : Fin 3) : W :=
  ⟨fun q=>if q=1 then factorRepresentative i else factorRepresentative j,1⟩

private theorem kind_eq_zero : ∀a:S4,kind a=0 ↔ a=1 := by decide +kernel

private theorem baseForm_class : ∀i j:Fin 3,(i≠0 ∨ j≠0) →
    baseForm i j=representative (pairIndex i j) ∨
      swap*baseForm i j*swap⁻¹=representative (pairIndex i j) := by decide +kernel

theorem involution_representative (x : W) (hxx : x*x=1) (hx1 : x≠1) :
    IsConj (representative (classIndex x)) x := by
  by_cases hx:x.right=1
  · have hi (i : C2) : x.left i*x.left i=1 := by
      have h := congrArg (fun w:W=>w.left i) hxx
      simpa [hx] using h
    choose a ha using fun i=>factor_involution_representative (x.left i) (hi i)
    let g : W := ⟨a,1⟩
    have hform : g*x*g⁻¹=baseForm (kind (x.left 1)) (kind (x.left turn)) := by
      apply RegularWreathProduct.ext
      · funext q
        rw [conjugate_left g x hx]
        simp only [g,inv_one,one_mul]
        rw [ha]
        rcases c2_eq_one_or_turn q with rfl|rfl
        · rfl
        · simp [baseForm,turn_ne_one]
      · simp [g,hx,baseForm]
    have hne : kind (x.left 1)≠0 ∨ kind (x.left turn)≠0 := by
      by_contra! h
      apply hx1
      apply RegularWreathProduct.ext
      · funext q
        rcases c2_eq_one_or_turn q with rfl|rfl
        · exact (kind_eq_zero _).mp h.1
        · exact (kind_eq_zero _).mp h.2
      · exact hx
    have hc : IsConj x (baseForm (kind (x.left 1)) (kind (x.left turn))) := isConj_iff.mpr ⟨g,hform⟩
    rw [classIndex,if_pos hx]
    rcases baseForm_class _ _ hne with he|he
    · rw [he] at hc
      exact hc.symm
    · exact (hc.trans (isConj_iff.mpr ⟨swap,he⟩)).symm
  · simpa [classIndex,hx,representative] using outside_involution_conjugate x hx hxx

theorem isConj_representative_iff (i : Fin 6) (x : W) :
    IsConj (representative i) x ↔ orderOf x=2 ∧ classIndex x=i := by
  constructor
  · intro hc
    obtain ⟨g,hg⟩ := isConj_iff.mp hc
    constructor
    · rw [←hg]
      exact ((MulAut.conj g).orderOf_eq (representative i)).trans (representative_order i)
    · rw [←hg,classIndex_conjugate,representative_index]
  · rintro ⟨ho,hi⟩
    rw [←hi]
    apply involution_representative
    · simpa only [pow_two,ho] using pow_orderOf_eq_one x
    · intro h
      simp [h] at ho

theorem representatives_not_conjugate {i j : Fin 6} (hij : i≠j) :
    ¬IsConj (representative i) (representative j) := by
  intro h
  have he := ((isConj_representative_iff i _).mp h).2
  rw [representative_index] at he
  exact hij he.symm

end SymmetricFourWreath.InvolutionClasses
