module
public import Theory.Representation.HermitianTensorThree.PointSection
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.Algebra.Module.ZMod

/-!
# The actual five-dimensional point-radical commutator

The point radical changes only the first row and column. A trace-one
commutator produces the central diagonal, and displacements of the other
diagonal matrices produce every off-diagonal coordinate. Thus its full
commutator span is the displayed five-space, of order 32.

This is the native calculation of V_z in Aschbacher–Smith H.4.6(4) and
8.2.11(2), printed pp.382 and 722, refs/quasithin.pdf. The source transport
retains the original radical image and the literal subgroup commutator.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Matrix.PSL3Even.UnipotentGeometry
open Representation.HermitianTensorThree.ImageOuter
namespace Representation.HermitianTensorThree.PointSection

private def movedAdd : AddSubgroup (Space 1) where
  carrier := {X : Space 1 | X.val 1 1 = 0 ∧ X.val 2 2 = 0 ∧ X.val 1 2 = 0}
  zero_mem' := ⟨rfl,rfl,rfl⟩
  add_mem' := by rintro X Y ⟨hx,hy,hz⟩ ⟨kx,ky,kz⟩; exact
    ⟨by simp [hx,kx],by simp [hy,ky],by simp [hz,kz]⟩
  neg_mem' := by
    rintro X ⟨hx,hy,hz⟩
    change -X.val 1 1=0 ∧ -X.val 2 2=0 ∧ -X.val 1 2=0
    exact ⟨by rw [hx,neg_zero],by rw [hy,neg_zero],by rw [hz,neg_zero]⟩

/-- The five-space supported on the first row and column. -/
def moved : Submodule (ZMod 2) (Space 1) := AddSubgroup.toZModSubmodule 2 movedAdd

theorem mem_moved (X : Space 1) : X ∈ moved ↔
    X.val 1 1=0 ∧ X.val 2 2=0 ∧ X.val 1 2=0 := Iff.rfl

/-- Coordinates retain the central diagonal and both off-diagonal entries. -/
@[expose] def movedCoordinates : moved ≃ (F 1 × E 1 × E 1) where
  toFun X := (⟨X.val.val 0 0,entry_conjugate 1 X.val 0 0⟩,X.val.val 0 1,X.val.val 0 2)
  invFun a := ⟨(coordinates 1).symm (![a.1,0,0],![a.2.1,a.2.2,0]),by exact ⟨rfl,rfl,rfl⟩⟩
  left_inv X := by
    apply Subtype.ext
    apply (coordinates 1).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Prod.ext
    · ext i
      fin_cases i
      · rfl
      · exact X.property.1.symm
      · exact X.property.2.1.symm
    · ext i
      fin_cases i
      · rfl
      · rfl
      · exact X.property.2.2.symm
  right_inv _ := rfl

theorem card_moved : Nat.card moved = 2^5 := by
  rw [Nat.card_congr movedCoordinates,Nat.card_prod,Nat.card_prod,card_F,card_E]
  norm_num

theorem finrank_moved : Module.finrank (ZMod 2) moved = 5 := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := moved)
  rw [card_moved,Nat.card_zmod] at hc
  exact (Nat.pow_right_inj (by decide : 1 < 2)).mp hc.symm

private def coord (a : F 1) (u v : E 1) : Space 1 :=
  (coordinates 1).symm (![a,0,0],![u,v,0])

private theorem coord_add (a b : F 1) (u v s t : E 1) :
    coord (a+b) (u+s) (v+t) = coord a u v + coord b s t := by
  apply (coordinates 1).injective
  simp only [map_add,coord,LinearEquiv.apply_symm_apply]
  ext i <;> fin_cases i <;> simp

/-- The point radical has exactly this five-dimensional commutator space. -/
theorem point_commutator :
    subspaceCommutator (UnipotentRadicals.ambientAction 1) ⊤
      (UnipotentRadicals.point 1) = moved := by
  let W := subspaceCommutator (UnipotentRadicals.ambientAction 1) ⊤
    (UnipotentRadicals.point 1)
  have hdiff (a c : E 1) (X : Space 1) :
      UnipotentRadicals.unipotentHom 1 ⟨a,0,c⟩ X - X ∈ W :=
    Submodule.subset_span ⟨_,mem_map_of_mem _ ((mem_V₁ _ _).mpr rfl),X,Submodule.mem_top, rfl⟩
  have hp : pointVector ∈ W := by
    obtain ⟨t,ht⟩ := FieldSections.exists_sigma_ne 1
    have hn : t+sigma 1 t ≠ 0 := fun hz => ht (CharTwo.add_eq_zero.mp hz).symm
    have hf : sigma 1 (t+sigma 1 t) = t+sigma 1 t := by
      rw [map_add,sigma_involutive,add_comm]
    have h1 : t+sigma 1 t=1 := (eq_zero_or_one_of_sq_eq_self hf).resolve_left hn
    have he : UnipotentRadicals.unipotentHom 1 ⟨1,0,0⟩ (coord 0 t 0) - coord 0 t 0 =
        pointVector := by
      apply Subtype.ext
      change matrix (E 1) ⟨1,0,0⟩ * (coord 0 t 0).val * adjoint 1 (matrix (E 1) ⟨1,0,0⟩) -
        (coord 0 t 0).val = pointVector.val
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [coord,coordinates,pointVector,matrix,adjoint,Matrix.vecMul,dotProduct,Fin.sum_univ_three]
      simpa only [add_comm] using h1
    exact he ▸ hdiff 1 0 (coord 0 t 0)
  have hd (a : F 1) : coord a 0 0 ∈ W := by
    rcases eq_zero_or_one_of_sq_eq_self (show a.val^2=a.val from a.property) with ha | ha
    · have he : a=0 := Subtype.ext ha
      subst a
      have he : coord 0 0 0=0 := by
        apply (coordinates 1).injective
        simp [coord]
      rw [he]
      exact W.zero_mem
    · have he : a=1 := Subtype.ext ha
      subst a
      exact hp
  have hu (u : E 1) : coord 0 u 0 ∈ W := by
    let a : F 1 := ⟨u*sigma 1 u,by
      change sigma 1 (_ * sigma 1 _) = _
      rw [map_mul,sigma_involutive,mul_comm]⟩
    let X : Space 1 := (coordinates 1).symm (![0,1,0],0)
    have he : UnipotentRadicals.unipotentHom 1 ⟨u,0,0⟩ X - X =
        coord a 0 0 + coord 0 u 0 := by
      apply Subtype.ext
      change matrix (E 1) ⟨u,0,0⟩ * X.val * adjoint 1 (matrix (E 1) ⟨u,0,0⟩) - X.val = _
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [X,a,coord,coordinates,matrix,adjoint,Matrix.vecMul,dotProduct,Fin.sum_univ_three]
    exact (Submodule.add_mem_iff_right _ (hd a)).mp (he ▸ hdiff u 0 X)
  have hv (v : E 1) : coord 0 0 v ∈ W := by
    let a : F 1 := ⟨v*sigma 1 v,by
      change sigma 1 (_ * sigma 1 _) = _
      rw [map_mul,sigma_involutive,mul_comm]⟩
    let X : Space 1 := (coordinates 1).symm (![0,0,1],0)
    have he : UnipotentRadicals.unipotentHom 1 ⟨0,0,v⟩ X - X =
        coord a 0 0 + coord 0 0 v := by
      apply Subtype.ext
      change matrix (E 1) ⟨0,0,v⟩ * X.val * adjoint 1 (matrix (E 1) ⟨0,0,v⟩) - X.val = _
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [X,a,coord,coordinates,matrix,adjoint,Matrix.vecMul,dotProduct,Fin.sum_univ_three]
    exact (Submodule.add_mem_iff_right _ (hd a)).mp (he ▸ hdiff 0 v X)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨a,ha,rfl⟩,X,_,rfl⟩
    have hy := (mem_V₁ (E 1) a).mp ha
    change (matrix (E 1) a * X.val * adjoint 1 (matrix (E 1) a)) 1 1 - X.val 1 1 = 0 ∧
      (matrix (E 1) a * X.val * adjoint 1 (matrix (E 1) a)) 2 2 - X.val 2 2 = 0 ∧
      (matrix (E 1) a * X.val * adjoint 1 (matrix (E 1) a)) 1 2 - X.val 1 2 = 0
    simp [matrix,hy,adjoint,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three]
  · intro X hX
    obtain ⟨⟨a,u,v⟩,he⟩ := movedCoordinates.symm.surjective ⟨X,hX⟩
    have he : coord a u v = X := congrArg Subtype.val he
    rw [←he]
    have hh := W.add_mem (W.add_mem (hd a) (hu u)) (hv v)
    simpa only [←coord_add,add_zero,zero_add] using hh

end Representation.HermitianTensorThree.PointSection
