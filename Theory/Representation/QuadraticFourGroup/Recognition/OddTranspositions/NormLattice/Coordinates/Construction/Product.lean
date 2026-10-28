module

public import Theory.GroupTheory.PairedProduct
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Coordinate generators for products of pairs

Regrouping coordinates indexed by `I × Bool` gives a product of pairs.
The equal-coordinate singletons generate the paired diagonal; the two axes
at one index generate the full pair subgroup. These calculations retain the
literal single-coordinate embeddings used by the component construction.

Source: the direct-product formulation in GLS2, Chapter B, Lemma 3.25.
-/

@[expose] public section

open Subgroup
namespace Representation.QuadraticFourGroup.PairConstruction
variable {I S : Type*} [Group S]

def pairedEquiv : ((I × Bool) → S) ≃* (I → S × S) where
  toFun f i := (f (i,false), f (i,true))
  invFun f p := if p.2 then (f p.1).2 else (f p.1).1
  left_inv f := by funext ⟨i,s⟩; cases s <;> rfl
  right_inv f := rfl
  map_mul' _ _ := rfl

theorem pairedEquiv_single [DecidableEq I] (i : I) (s : Bool) (x : S) :
    pairedEquiv (Pi.mulSingle (i,s) x) =
      Pi.mulSingle i (if s then (1,x) else (x,1)) := by
  funext j
  by_cases hji : j = i
  · subst j; cases s <;> simp [pairedEquiv]
  · cases s <;> simp [pairedEquiv, hji]

def diagonalSingle [DecidableEq I] (i : I) : S →* (I → S × S) :=
  (MonoidHom.mulSingle (fun _ : I => S × S) i).comp
    ((MonoidHom.id S).prod (MonoidHom.id S))

theorem diagonal_generate [Fintype I] [DecidableEq I] :
    (⨆ i : I, (diagonalSingle (S := S) i).range) = PairedProduct.diagonal I S := by
  apply le_antisymm
  · apply iSup_le
    intro i f hf
    obtain ⟨x,rfl⟩ := hf
    intro j
    by_cases hji : j = i
    · subst j; simp [diagonalSingle]
    · simp [diagonalSingle, Pi.mulSingle_eq_of_ne hji]
  · intro f hf
    rw [← Finset.noncommProd_mulSingle f]
    apply Subgroup.noncommProd_mem
    intro i _
    apply (le_iSup (fun i : I => (diagonalSingle (S := S) i).range) i)
    refine ⟨(f i).1, ?_⟩
    change (Pi.mulSingle i ((f i).1,(f i).1) : I → S × S) = Pi.mulSingle i (f i)
    congr 1
    exact Prod.ext rfl (hf i)

def axisSingle [DecidableEq I] (i : I) (s : Bool) : S →* (I → S × S) :=
  (MonoidHom.mulSingle (fun _ : I => S × S) i).comp
    (if s then MonoidHom.inr S S else MonoidHom.inl S S)

theorem axisSingle_apply [DecidableEq I] (i : I) (s : Bool) (x : S) :
    axisSingle i s x = Pi.mulSingle i (if s then (1,x) else (x,1)) := by
  cases s <;> rfl

theorem axis_generate [DecidableEq I] (i : I) :
    (axisSingle (S := S) i false).range ⊔ (axisSingle (S := S) i true).range =
      PairedProduct.factor I S i := by
  apply le_antisymm
  · apply sup_le <;> rintro f ⟨x,rfl⟩ j hji <;>
      exact Pi.mulSingle_eq_of_ne hji _
  · intro f hf
    have he : axisSingle i false (f i).1 * axisSingle i true (f i).2 = f := by
      funext j
      by_cases hji : j = i
      · subst j; simp [axisSingle]
      · simp [axisSingle, Pi.mulSingle_eq_of_ne hji, hf j hji]
    rw [← he]
    exact mul_mem (mem_sup_left ⟨_,rfl⟩) (mem_sup_right ⟨_,rfl⟩)

end Representation.QuadraticFourGroup.PairConstruction

end
