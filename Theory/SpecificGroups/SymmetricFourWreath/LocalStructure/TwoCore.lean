module
public import Theory.SpecificGroups.SymmetricFourWreath.LocalStructure.Coordinates
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
public import Theory.GroupTheory.WreathTwoResidual
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# The actual two-core of the symmetric-four wreath product

Quotienting each S4 factor by its normal Klein four gives a surjection to
S3 wreath C2. The existing natural two-plane actor theorem gives trivial
two-core in that quotient. Its kernel is precisely the displayed A, so
A is the actual two-core of the original local model.

Source: Aschbacher–Smith 13.9.2 setup, printed p.969 (PDF p.986).
-/

public section
namespace SymmetricFourWreath
open Subgroup
private abbrev S3 := Equiv.Perm (Fin 3)
private abbrev W3 := RegularWreathProduct S3 C2
private instance : DecidablePred (·∈(plane true).map square) := fun x=>
  inferInstanceAs (Decidable (∃a,a∈plane true ∧ square a=x))

private theorem plane_true_core (x : S4) :
    x∈(plane true).map square ↔ x∈Theory.SpecificGroups.SymmetricSix.DuadCalculation.core := by
  revert x
  decide +kernel

private def wreathQuotient : W→*W3 where
  toFun x := ⟨fun i=>Theory.SpecificGroups.SymmetricSix.DuadCalculation.quotientHom (x.left i),x.right⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp

private theorem wreathQuotient_surjective : Function.Surjective wreathQuotient := by
  intro x
  choose a ha using fun i=>Theory.SpecificGroups.SymmetricSix.DuadCalculation.quotientHom_surjective (x.left i)
  exact ⟨⟨a,x.right⟩,RegularWreathProduct.ext (funext ha) rfl⟩

private theorem wreathQuotient_ker : wreathQuotient.ker=A := by
  ext x
  rw [MonoidHom.mem_ker,mem_elementary]
  constructor
  · intro hx
    have hr := congrArg RegularWreathProduct.right hx
    have hl (i : C2) := congrArg (fun w:W3=>w.left i) hx
    exact ⟨hr,(plane_true_core _).mpr (hl 1),(plane_true_core _).mpr (hl turn)⟩
  · rintro ⟨hr,ha,hb⟩
    apply RegularWreathProduct.ext
    · funext i
      rcases c2_eq_one_or_turn i with rfl|rfl
      · exact (plane_true_core _).mp ha
      · exact (plane_true_core _).mp hb
    · exact hr

private theorem wreathThree_twoCore : pCore 2 W3=⊥ := by
  let e := RegularWreathProduct.congr
    (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three).symm (MulEquiv.refl C2)
  apply (map_injective (f:=e.toMonoidHom) e.injective)
  rw [pCore_map_iso,Theory.GroupTheory.WreathTwoResidual.twoCore_eq_bot,Subgroup.map_bot]

theorem A_eq_twoCore : A=pCore 2 W := by
  have hn : A.Normal := wreathQuotient_ker ▸ inferInstance
  have hp : IsPGroup 2 A := IsElementaryAbelian.isPGroup 2 A
  apply le_antisymm
  · exact le_sSup ⟨hn,hp⟩
  have hm : ((pCore 2 W).map wreathQuotient).Normal :=
    (inferInstance : (pCore 2 W).Normal).map _ wreathQuotient_surjective
  have hle : (pCore 2 W).map wreathQuotient ≤ pCore 2 W3 :=
    le_sSup ⟨hm,pCore_isPGroup.map wreathQuotient⟩
  rw [wreathThree_twoCore] at hle
  rw [←wreathQuotient_ker]
  exact (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp hle)
end SymmetricFourWreath
