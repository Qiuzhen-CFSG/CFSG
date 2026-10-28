module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.LocalDihedralGeometry.Contracts
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# The marked four-group by symmetric-six centralizer

The four-group is represented by two binary coordinates. An odd permutation
acts by the shear `(i,j) ↦ (i+j,j)`, fixing the first generator. On ten letters,
its two generators are `(01)(23)` and `(02)(13)`, and a six-letter permutation
is accompanied by `(01)` precisely when it is odd. This gives an injective
map into A10. Its image is the full centralizer of `(01)(23)` by the known
centralizer order 2880. Only the four-group and its involutory action use
finite certificates; no enumeration of A10 is needed.

Source: Held, Illinois J. Math. 13 (1969), Lemmas 4.2 and 5.4,
DOI 10.1215/ijm/1256053756, pp.232,236–237.
-/

@[expose] public section

open Equiv Subgroup
open Theory.GroupTheory.HeldM22A10
open Theory.GroupTheory.HeldM22A10.A10Identification
open Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry.MuCentralizerConstruction
abbrev Four := Multiplicative (ZMod 2 × ZMod 2)
def first : Four := Multiplicative.ofAdd (1, 0)
def second : Four := Multiplicative.ofAdd (0, 1)
def flip : MulAut Four where
  toFun x := Multiplicative.ofAdd (x.toAdd.1 + x.toAdd.2, x.toAdd.2)
  invFun x := Multiplicative.ofAdd (x.toAdd.1 + x.toAdd.2, x.toAdd.2)
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

def signAction : ℤˣ →* MulAut Four where
  toFun u := if u = 1 then 1 else flip
  map_one' := by simp
  map_mul' u v := by
    rcases Int.units_eq_one_or u with rfl | rfl <;>
      rcases Int.units_eq_one_or v with rfl | rfl <;>
      ext x <;> revert x <;> decide +kernel

def action : Perm (Fin 6) →* MulAut Four := signAction.comp Perm.sign
abbrev Model := Four ⋊[action] Perm (Fin 6)
instance : Finite Model := Finite.of_equiv (Four × Perm (Fin 6)) SemidirectProduct.equivProd.symm

def fourPerm : Four →* Perm (Fin 4) where
  toFun x := (swap 0 1 * swap 2 3) ^ x.toAdd.1.val *
    (swap 0 2 * swap 1 3) ^ x.toAdd.2.val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem fourPerm_injective : Function.Injective fourPerm := by decide +kernel

def signSwap : ℤˣ →* Perm (Fin 4) where
  toFun u := if u = 1 then 1 else swap 0 1
  map_one' := by simp
  map_mul' u v := by
    rcases Int.units_eq_one_or u with rfl | rfl <;>
      rcases Int.units_eq_one_or v with rfl | rfl <;> decide +kernel

theorem four_action (u : ℤˣ) (k : Four) :
    fourPerm (signAction u k) = signSwap u * fourPerm k * (signSwap u)⁻¹ := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> revert k <;> decide +kernel

def block : Perm (Fin 4) × Perm (Fin 6) →* Perm (Fin 10) :=
  (permCongrHom finSumFinEquiv).toMonoidHom.comp (Perm.sumCongrHom _ _)

theorem block_injective : Function.Injective block :=
  (permCongrHom finSumFinEquiv).injective.comp Perm.sumCongrHom_injective

theorem block_sign (p : Perm (Fin 4)) (q : Perm (Fin 6)) :
    Perm.sign (block (p, q)) = Perm.sign p * Perm.sign q := by
  change Perm.sign (finSumFinEquiv.permCongr (sumCongr p q)) = _
  rw [Perm.sign_permCongr, Perm.sign_sumCongr]

def blocks : Model →* Perm (Fin 4) × Perm (Fin 6) :=
  SemidirectProduct.lift (fourPerm.prod (1 : Four →* Perm (Fin 6)))
    ((signSwap.comp Perm.sign).prod (MonoidHom.id _)) (by
      intro p
      apply MonoidHom.ext
      intro k
      apply Prod.ext
      · exact four_action (Perm.sign p) k
      · simp)

theorem blocks_apply (x : Model) :
    blocks x = (fourPerm x.left * signSwap (Perm.sign x.right), x.right) := by
  simp [blocks, SemidirectProduct.lift]

theorem blocks_injective : Function.Injective blocks := by
  intro x y h
  rw [blocks_apply, blocks_apply] at h
  have hr := congrArg Prod.snd h
  have hl := congrArg Prod.fst h
  change x.right = y.right at hr
  change fourPerm x.left * signSwap (Perm.sign x.right) =
    fourPerm y.left * signSwap (Perm.sign y.right) at hl
  rw [hr] at hl
  exact SemidirectProduct.ext (fourPerm_injective (mul_right_cancel hl)) hr

def tenHom : Model →* Perm (Fin 10) := block.comp blocks

theorem tenHom_even (x : Model) : tenHom x ∈ alternatingGroup (Fin 10) := by
  rw [Perm.mem_alternatingGroup]
  change Perm.sign (block (blocks x)) = 1
  rw [blocks_apply, block_sign, map_mul]
  have hf : Perm.sign (fourPerm x.left) = 1 :=
    (by decide +kernel : ∀ k, Perm.sign (fourPerm k) = 1) x.left
  have hs : Perm.sign (signSwap (Perm.sign x.right)) = Perm.sign x.right := by
    rcases Int.units_eq_one_or (Perm.sign x.right) with h | h <;> rw [h] <;> decide +kernel
  rw [hf, hs, one_mul]
  exact Int.units_mul_self _

def altHom : Model →* alternatingGroup (Fin 10) := tenHom.codRestrict _ tenHom_even

theorem ten_first : tenHom (SemidirectProduct.inl first) =
    (doubleTransposition : Perm (Fin 10)) := by decide +kernel

theorem first_central (x : Model) :
    Commute (SemidirectProduct.inl first : Model) x := by
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply]
    change first * x.left = x.left * action x.right first
    have hf : action x.right first = first := by
      rcases Int.units_eq_one_or (Perm.sign x.right) with h | h <;>
        change signAction (Perm.sign x.right) first = first <;> rw [h] <;> decide +kernel
    rw [hf, mul_comm]
  · simp

def modelHom : Model →* SevenConstruction.SplitFactor.LocalDihedralGeometry.MuModel :=
  altHom.codRestrict _ (fun x => mem_centralizer_singleton_iff.mpr (by
    have h := (first_central x).symm.map tenHom
    apply Subtype.ext
    change tenHom x * (doubleTransposition : Perm (Fin 10)) =
      (doubleTransposition : Perm (Fin 10)) * tenHom x
    rw [← ten_first]
    exact h.eq))

theorem modelHom_injective : Function.Injective modelHom := by
  intro x y h
  apply blocks_injective
  apply block_injective
  exact congrArg (fun z : SevenConstruction.SplitFactor.LocalDihedralGeometry.MuModel =>
    ((z : alternatingGroup (Fin 10)) : Perm (Fin 10))) h

theorem model_card : Nat.card Model = 2880 := by
  rw [SemidirectProduct.card]
  norm_num [Four, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

noncomputable def modelEquiv : Model ≃*
    SevenConstruction.SplitFactor.LocalDihedralGeometry.MuModel :=
  MulEquiv.ofBijective modelHom (modelHom_injective.bijective_of_nat_card_le (by
    rw [model_card, centralizer_noncentral_card]))

theorem modelEquiv_first : modelEquiv (SemidirectProduct.inl first) =
    SevenConstruction.SplitFactor.LocalDihedralGeometry.modelMu := by
  apply Subtype.ext
  apply Subtype.ext
  exact ten_first

def fourCoordinates : Four →* CentralizerModels.a10Centralizer where
  toFun x := modelElement 1 ^ x.toAdd.1.val * modelElement 6 ^ x.toAdd.2.val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem fourCoordinates_first : fourCoordinates first = modelElement 1 := by decide +kernel

theorem fourCoordinates_second : fourCoordinates second = modelElement 6 := by decide +kernel

theorem fourCoordinates_flip (k : Four) :
    fourCoordinates (flip k) = modelElement 2 * fourCoordinates k * (modelElement 2)⁻¹ := by
  revert k
  decide +kernel

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry.MuCentralizerConstruction
