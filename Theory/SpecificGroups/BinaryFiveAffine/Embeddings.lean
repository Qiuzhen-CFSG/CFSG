module
public import Theory.SpecificGroups.BinaryFiveAffine.Basic
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
import Mathlib.Tactic
/-!
# Marked D₈ and S₄ embeddings in the binary affine five-point group

The D₈ factor acts on the two-plane with basis (1,0,1,1,1) and
(0,1,1,1,1). The S₄ factor is its affine action on the last-three Klein
four-group: the translation is the image of 0 and the linear part is
its established action on the three double transpositions. Coordinate
identities verify the two small homomorphisms and their commutation.
The marked pair vector is the square of the D₈ rotation.

Source: Aschbacher–Smith 13.9.10. No subgroup census is used.
-/
@[expose] public section
namespace BinaryFiveAffine
open Theory.SpecificGroups.SymmetricSix.DuadCalculation
def tailPerm : Equiv.Perm (Fin 3) →* S :=
  (finSumFinEquiv : Fin 2 ⊕ Fin 3 ≃ Fin 5).permCongrHom.toMonoidHom.comp
    ((Equiv.Perm.sumCongrHom (Fin 2) (Fin 3)).comp (MonoidHom.inr _ _))

@[simp] theorem tailPerm_zero (g : Equiv.Perm (Fin 3)) : tailPerm g 0 = 0 := rfl
@[simp] theorem tailPerm_one (g : Equiv.Perm (Fin 3)) : tailPerm g 1 = 1 := rfl

def tailVector (i : Fin 4) : V := Multiplicative.ofAdd
  ⟨if i = 0 then 0 else if i = 1 then ![0,0,0,1,1]
    else if i = 2 then ![0,0,1,0,1] else ![0,0,1,1,0], by
    fin_cases i <;> decide +kernel⟩

def symmetricRaw (g : Equiv.Perm (Fin 4)) : W :=
  ⟨tailVector (g 0), tailPerm (quotientHom g)⟩

set_option maxRecDepth 10000 in
theorem symmetricRaw_mul (g h : Equiv.Perm (Fin 4)) :
    symmetricRaw (g*h) = symmetricRaw g * symmetricRaw h := by
  apply SemidirectProduct.ext
  · apply Subtype.ext
    have hc : ∀ g h : Equiv.Perm (Fin 4), ∀ i : Fin 5,
        (tailVector ((g*h) 0)).toAdd.val i =
        (tailVector (g 0)).toAdd.val i +
          (tailVector (h 0)).toAdd.val ((tailPerm (quotientHom g))⁻¹ i) := by decide +kernel
    exact funext (hc g h)
  · exact (tailPerm.comp quotientHom).map_mul g h

def symmetricEmbedding : Equiv.Perm (Fin 4) →* W where
  toFun := symmetricRaw
  map_one' := by apply SemidirectProduct.ext <;> decide +kernel
  map_mul' := symmetricRaw_mul


theorem tailPerm_injective : Function.Injective tailPerm :=
  (finSumFinEquiv : Fin 2 ⊕ Fin 3 ≃ Fin 5).permCongrHom.injective.comp
    (Equiv.Perm.sumCongrHom_injective.comp (fun _ _ h => congrArg Prod.snd h))

theorem tailVector_injective : Function.Injective tailVector := by decide +kernel

set_option maxRecDepth 10000 in
theorem symmetricEmbedding_injective : Function.Injective symmetricEmbedding := by
  have h : ∀ g h : Equiv.Perm (Fin 4), g 0 = h 0 → quotientHom g = quotientHom h → g = h := by
    decide +kernel
  intro g k he
  exact h g k (tailVector_injective (congrArg SemidirectProduct.left he))
    (tailPerm_injective (congrArg SemidirectProduct.right he))

def rotationVector (i : ZMod 4) : V := Multiplicative.ofAdd
  ⟨if i = 0 then 0 else if i = 1 then ![1,0,1,1,1]
    else if i = 2 then ![1,1,0,0,0] else ![0,1,1,1,1], by
    fin_cases i <;> decide +kernel⟩

def dihedralRaw : DihedralGroup 4 → W
  | .r i => ⟨rotationVector i, if i.val % 2 = 0 then 1 else Equiv.swap 0 1⟩
  | .sr i => ⟨action (Equiv.swap 0 1) (rotationVector i),
      if i.val % 2 = 0 then Equiv.swap 0 1 else 1⟩

set_option maxRecDepth 10000 in
theorem dihedralRaw_mul (g h : DihedralGroup 4) :
    dihedralRaw (g*h) = dihedralRaw g * dihedralRaw h := by
  apply SemidirectProduct.ext
  · have hc : ∀ g h : DihedralGroup 4,
        (dihedralRaw (g*h)).left = (dihedralRaw g * dihedralRaw h).left := by decide +kernel
    exact hc g h
  · have hc : ∀ g h : DihedralGroup 4,
        (dihedralRaw (g*h)).right = (dihedralRaw g * dihedralRaw h).right := by decide +kernel
    exact hc g h

def dihedralEmbedding : DihedralGroup 4 →* W where
  toFun := dihedralRaw
  map_one' := by apply SemidirectProduct.ext <;> decide +kernel
  map_mul' := dihedralRaw_mul

set_option maxRecDepth 10000 in
theorem dihedralEmbedding_injective : Function.Injective dihedralEmbedding := by
  have hc : ∀ g h : DihedralGroup 4,
      (dihedralRaw g).left = (dihedralRaw h).left →
      (dihedralRaw g).right = (dihedralRaw h).right → g = h := by decide +kernel
  intro g h he
  exact hc g h (congrArg SemidirectProduct.left he) (congrArg SemidirectProduct.right he)

theorem dihedral_marked : dihedralEmbedding (.r 2) = t := by
  apply SemidirectProduct.ext <;> decide +kernel

set_option maxRecDepth 10000 in
theorem embeddings_commute (r : DihedralGroup 4) (s : Equiv.Perm (Fin 4)) :
    Commute (dihedralEmbedding r) (symmetricEmbedding s) := by
  change dihedralEmbedding r * symmetricEmbedding s = symmetricEmbedding s * dihedralEmbedding r
  apply SemidirectProduct.ext
  · have hc : ∀ r : DihedralGroup 4, ∀ s : Equiv.Perm (Fin 4),
      (dihedralRaw r * symmetricRaw s).left = (symmetricRaw s * dihedralRaw r).left := by decide +kernel
    exact hc r s
  · have hc : ∀ r : DihedralGroup 4, ∀ s : Equiv.Perm (Fin 4),
      (dihedralRaw r * symmetricRaw s).right = (symmetricRaw s * dihedralRaw r).right := by decide +kernel
    exact hc r s

end BinaryFiveAffine
