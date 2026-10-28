module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.SymmetricFacts

/-!
# The normal S₃ configuration in B.5.6(2)

When the actual offender restriction is the symmetric-three alternative,
its single factor and its commutator support give the two marked product
maps required by 13.6.13. Residual and Thompson equalities come from the
original X-family and Sylow image; no decomposition or irreducibility
hypothesis is added. Other classification branches remain separate.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6(2), printed p.105, and 13.6.13, printed p.929.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
variable {G : Type*} [Group G]

/-- Construct every field of the actual normal-factor configuration for
B.5.6(2), including the coordinate inclusions and the ambient supports. -/
theorem normalS3Decomposition_of_symmetricThree [Finite G]
    (L T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)] (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    {X : Subgroup (Gstar z v)} (hX : X ∈ XFamily L T z v)
    (c : ChapterB.SourceInduction.SymmetricThreeCase
      (FFFactors.offenderRepresentation (starRepresentation z v))) :
    Nonempty (NormalS3Decomposition z v X) := by
  classical
  let H := FFFactors.offenderActor (starRepresentation z v)
  have hu := symmetricThree_support z v c
  have hs : factorSupport z v H H = movedSubgroup z v H := hu.1
  have hc : Nat.card (factorSupport z v H H) = 4 := by rw [hs]; exact hu.2
  refine ⟨{
    H := H
    normal := inferInstance
    count := 1
    count_pos := by decide
    count_le_two := by decide
    factor := fun _ => H
    factor_le := fun _ => le_rfl
    model := fun _ => c.equiv
    product := MulEquiv.piUnique (fun _ : Fin 1 => H)
    product_single := ?_
    residual_eq := symmetricThree_residual_eq L T z v hz S hS hX c
    thompson_eq := symmetricThree_thompson_eq L T z v hz S hS hX c
    space := (MulEquiv.piUnique (fun _ : Fin 1 => factorSupport z v H H)).trans
      (MulEquiv.subgroupCongr hs)
    space_single := ?_
    support_card := fun _ => hc }⟩
  · intro i a
    have hi : i = default := Subsingleton.elim _ _
    subst i
    change ((Pi.mulSingle (M := fun _ : Fin 1 => H) default a) default : Gstar z v) = a
    exact congrArg H.subtype (Pi.mulSingle_eq_same (M := fun _ : Fin 1 => H) default a)
  · intro i a
    have hi : i = default := Subsingleton.elim _ _
    subst i
    change ((Pi.mulSingle (M := fun _ : Fin 1 => factorSupport z v H H) default a) default : G) = a
    exact congrArg (factorSupport z v H H).subtype
      (Pi.mulSingle_eq_same (M := fun _ : Fin 1 => factorSupport z v H H) default a)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction
end
