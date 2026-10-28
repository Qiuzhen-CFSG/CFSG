module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Application.Source
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# Actual cubic factors of the solvable Thompson decomposition

The full B.2.16 exceptional datum includes an internal direct product of
PSL₂(2) factors. Their derived subgroups are the actual alternating cubics.
The definitions retain the literal star quotient and its factor inclusions;
finite kernel reduction identifies the derived subgroup of S₃ with A₃.
These cubic subgroups supply the residual Y construction in 15.4.12.

Source: Aschbacher–Smith B.2.16 and 15.4.12, printed pp.79 and1160–1161.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ThompsonFactors
open Chapter1.RadicalNormalizers.ThompsonSource
variable {H : Type*} [Group H] {S : Sylow 2 H}
  [IsElementaryAbelian 2 (closure S)]

abbrev Star := CentralQuotient (closure S)

def thompsonImage : Subgroup (Star (S := S)) :=
  (elementaryAbelianMaxJ (⊤ : Subgroup H)).map (starMap (closure S))

def productMap (d : Exceptional S) : ((i : Fin d.count) → d.factor i) →* Star (S := S) :=
  thompsonImage.subtype.comp d.groupProduct.toMonoidHom

theorem productMap_injective (d : Exceptional S) : Function.Injective (productMap d) :=
  Subtype.val_injective.comp d.groupProduct.injective

@[simp] theorem productMap_single (d : Exceptional S) (i : Fin d.count) (g : d.factor i) :
    productMap d (Pi.mulSingle i g) = g := d.groupProduct_single i g

theorem factor_le_thompsonImage (d : Exceptional S) (i : Fin d.count) :
    d.factor i ≤ thompsonImage := by
  intro g hg
  have he : (d.groupProduct (Pi.mulSingle i ⟨g,hg⟩) : Star (S := S)) = g :=
    d.groupProduct_single i ⟨g,hg⟩
  rw [← he]
  exact (d.groupProduct (Pi.mulSingle i ⟨g,hg⟩)).property

/-- The intrinsic alternating cubic of one actual symmetric-three factor. -/
def cubicFactor (d : Exceptional S) (i : Fin d.count) : Subgroup (Star (S := S)) :=
  (_root_.commutator (d.factor i)).map (d.factor i).subtype

/-- The rotations on a specified collection of actual factors. -/
def cubicProduct (d : Exceptional S) (I : Finset (Fin d.count)) : Subgroup (Star (S := S)) :=
  I.sup (cubicFactor d)

theorem cubicFactor_eq_commutator (d : Exceptional S) (i : Fin d.count) :
    cubicFactor d i = ⁅d.factor i,d.factor i⁆ := map_subtype_commutator _

theorem cubicFactor_le (d : Exceptional S) (i : Fin d.count) :
    cubicFactor d i ≤ d.factor i := map_subtype_le _

private theorem perm_three_commutator :
    _root_.commutator (Equiv.Perm (Fin 3)) = alternatingGroup (Fin 3) := by
  let r : Equiv.Perm (Fin 3) := ⁅Equiv.swap (0 : Fin 3) 1, Equiv.swap (1 : Fin 3) 2⁆
  have hr : r ∈ _root_.commutator (Equiv.Perm (Fin 3)) :=
    commutator_mem_commutator (mem_top _) (mem_top _)
  have hh : ∀ g : Equiv.Perm (Fin 3), g ∈ alternatingGroup (Fin 3) →
      g = 1 ∨ g = r ∨ g = r^2 := by
    simp only [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  apply le_antisymm alternatingGroup.commutator_perm_le
  intro g hg
  rcases hh g hg with h | h | h
  · rw [h]; exact one_mem _
  · rw [h]; exact hr
  · rw [h]; exact pow_mem hr _

/-- This is a concrete S₃ marking of each original factor. -/
def factorModel (d : Exceptional S) (i : Fin d.count) : d.factor i ≃* Equiv.Perm (Fin 3) :=
  (d.factorModel i).trans (Matrix.SpecialLinearGroup.sl2TwoEquivPSL2Two.symm.trans
    (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three))

theorem cubicFactor_card (d : Exceptional S) (i : Fin d.count) :
    Nat.card (cubicFactor d i) = 3 := by
  let e := factorModel d i
  have he : (_root_.commutator (d.factor i)).map e.toMonoidHom =
      alternatingGroup (Fin 3) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    exact perm_three_commutator
  rw [cubicFactor, card_map_of_injective (d.factor i).subtype_injective,
    ← card_map_of_injective (K := _root_.commutator (d.factor i))
      (f := e.toMonoidHom) e.injective, he, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

theorem cubicFactor_conj (d : Exceptional S) (g : Star (S := S))
    (i j : Fin d.count)
    (h : (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor j) :
    (cubicFactor d i).map (MulAut.conj g).toMonoidHom = cubicFactor d j := by
  rw [cubicFactor_eq_commutator, map_commutator, h, cubicFactor_eq_commutator]

end CFSG.Quasithin.Chapter15.Section04.FamilySource.ThompsonFactors
