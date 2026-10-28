module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ModelPlacement.SmallRankOuter
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.CyclicOuter
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
public import Theory.SpecificGroups.Triality.OuterOddSubgroups
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups

/-!
# Abelian outer action in the large-field component catalogue

The actual binary models have cyclic outer quotient except possibly the two
signed degree-three families. This uses the full proved automorphism coverage
on each carrier, inheriting simplicity and perfectness from the actual component.
The remaining signed-three cases are treated directly on their root subgroups
in SourceSignedThree, without a whole-extension classification.

Source: Aschbacher--Smith 13.6.6, printed p.927.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
open InitialSieve
/-- The only potentially nonabelian outer groups in the large-field list are
those of the two signed degree-three families. -/
theorem outer_abelian_or_signedThree
    {D : Type*} [Group D] [Finite D] [IsSimpleGroup D] [Group.IsPerfect D]
    {m : ℕ} (hm : 1 < m) (hmodel : BinaryModelAt D m) :
    IsMulCommutative (MulAut.Outer D) ∨ ClassicalGroup.IsPSL D 3 (2 ^ m) ∨
      ClassicalGroup.IsPSU D 3 (2 ^ m) := by
  cases hmodel with
  | linear_two n hn iso =>
    left
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := iso
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let := Theory.PSL2.OuterSolvable.charTwo_outer_isCyclic (F := F)
    let := (MulAut.outerCongr e).isCyclic.mpr inferInstance
    infer_instance
  | unitary_three n hn iso => exact Or.inr (Or.inr iso)
  | linear_three n hn iso => exact Or.inr (Or.inl iso)
  | suzuki n hn iso =>
    left
    obtain ⟨e⟩ := iso
    let := BenderSuzuki.MatrixGroups.suzuki_outer_isCyclic n hn
    let := (MulAut.outerCongr e).isCyclic.mpr inferInstance
    infer_instance
  | symplectic n hn iso =>
    left
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := iso
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let e' := e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
    let := Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.outer_isCyclic_of_card
      hF hm Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram
    let := (MulAut.outerCongr e').isCyclic.mpr inferInstance
    infer_instance
  | g2 n hn iso =>
    left
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := iso
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    have hq : 2 < Nat.card F := by
      rw [hF]
      exact (show (2:ℕ)^1 < 2^m from Nat.pow_lt_pow_right (by decide) hm)
    let := Atlas.G2.LieAutomorphismExtensions.outer_isCyclic hq
    let := (MulAut.outerCongr e).isCyclic.mpr inferInstance
    infer_instance
  | triality n hn iso =>
    left
    obtain ⟨P,hP,⟨e⟩⟩ := iso
    let : IsSimpleGroup (Triality.Standard.Carrier P) := e.isSimpleGroup_congr.mp inferInstance
    let : Group.IsPerfect (Triality.Standard.Carrier P) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    let := Triality.Standard.OuterOdd.outer_isCyclic P m hn hP
    let := (MulAut.outerCongr e).isCyclic.mpr inferInstance
    infer_instance
  | ree n hn iso =>
    left
    obtain ⟨d,⟨e⟩⟩ := iso
    let : IsSimpleGroup d.fixedGroup := e.isSimpleGroup_congr.mp inferInstance
    let : Group.IsPerfect d.fixedGroup := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    let := ReeF4.LocalBlockInput.outer_isCyclic hn d
    let := (MulAut.outerCongr e).isCyclic.mpr inferInstance
    infer_instance
  | symplectic_derived _ => omega
  | g2_derived _ => omega
  | tits _ => omega
  | binary_linear _ _ _ => omega
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
